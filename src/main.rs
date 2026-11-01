use exif::{In as ExifIfd, Reader as ExifReader, Tag as ExifTag, Value as ExifValue};
use gpui::{
    Animation, AnimationExt, App, Application, Bounds, Context, Element, ElementId, GlobalElementId,
    Hitbox, HitboxBehavior, InspectorElementId, LayoutId, ObjectFit, PathPromptOptions, FocusHandle, Focusable, Entity, EntityInputHandler, ElementInputHandler, UTF16Selection, ShapedLine, TextRun, CursorStyle, MouseButton, MouseDownEvent, PaintQuad, Pixels, Point, Style, ClipboardItem, fill, point, actions,
    Render, ScrollStrategy, SharedString, StyledText, UniformListScrollHandle, Window, WindowBounds,
    WindowOptions, deferred, div, img, prelude::*, px, relative, rgb, rgba, size, surface, uniform_list,
};
use objc2::{AnyThread, MainThreadMarker, rc::Retained, runtime::AnyObject};
use objc2_av_foundation::{AVPlayer, AVPlayerItem, AVPlayerItemVideoOutput};
use objc2_core_media::CMTime;
use objc2_foundation::{NSDictionary, NSNumber, NSString, NSURL};
use sha2::{Digest, Sha256};
use std::{
    cell::Cell,
    ops::Range,
    collections::{BTreeMap, HashMap, HashSet},
    env, fs,
    hash::{Hash, Hasher},
    io::BufReader,
    path::{Path, PathBuf},
    process::Command,
    rc::Rc,
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};

struct SelectableText {
    id: ElementId,
    selection_key: u64,
    text: SharedString,
    layout: StyledText,
}

static ACTIVE_TEXT_SELECTION: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Default)]
struct SelectableTextState {
    selection: Rc<Cell<(usize, usize)>>,
    anchor: Rc<Cell<Option<usize>>>,
}

struct SelectableTextPrepaint {
    hitbox: Hitbox,
    selection: Rc<Cell<(usize, usize)>>,
    anchor: Rc<Cell<Option<usize>>>,
}

impl SelectableText {
    fn new(text: impl Into<SharedString>, id: impl Into<ElementId>) -> Self {
        let text = text.into();
        let id = id.into();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        format!("{id:?}").hash(&mut hasher);
        let selection_key = hasher.finish().max(1);
        Self { id, selection_key, layout: StyledText::new(text.clone()), text }
    }
}

impl IntoElement for SelectableText {
    type Element = Self;
    fn into_element(self) -> Self { self }
}

impl Element for SelectableText {
    type RequestLayoutState = ();
    type PrepaintState = SelectableTextPrepaint;

    fn id(&self) -> Option<ElementId> { Some(self.id.clone()) }
    fn source_location(&self) -> Option<&'static core::panic::Location<'static>> { None }

    fn request_layout(&mut self, id: Option<&GlobalElementId>, inspector: Option<&InspectorElementId>, window: &mut Window, cx: &mut App) -> (LayoutId, ()) {
        self.layout.request_layout(id, inspector, window, cx)
    }

    fn prepaint(&mut self, id: Option<&GlobalElementId>, inspector: Option<&InspectorElementId>, bounds: Bounds<gpui::Pixels>, state: &mut (), window: &mut Window, cx: &mut App) -> SelectableTextPrepaint {
        self.layout.prepaint(id, inspector, bounds, state, window, cx);
        window.with_element_state::<SelectableTextState, _>(id.expect("selectable text requires an element id"), |state, window| {
            let state = state.unwrap_or_default();
            let hitbox = window.insert_hitbox(bounds, HitboxBehavior::Normal);
            (SelectableTextPrepaint { hitbox, selection: state.selection.clone(), anchor: state.anchor.clone() }, state)
        })
    }

    fn paint(&mut self, id: Option<&GlobalElementId>, inspector: Option<&InspectorElementId>, bounds: Bounds<gpui::Pixels>, state: &mut (), select_state: &mut SelectableTextPrepaint, window: &mut Window, cx: &mut App) {
        let text_layout = self.layout.layout().clone();
        let selection = select_state.selection.clone();
        let anchor = select_state.anchor.clone();
        let hitbox = select_state.hitbox.clone();
        let selection_key = self.selection_key;
        let is_selecting = anchor.get().is_some();
        if hitbox.is_hovered(window) {
            let hitbox_for_mouse = hitbox.clone();
            window.on_mouse_event(move |event: &gpui::MouseDownEvent, phase, window, cx| {
                if phase == gpui::DispatchPhase::Bubble && hitbox_for_mouse.is_hovered(window) && event.button == gpui::MouseButton::Left {
                    if let Ok(index) = text_layout.index_for_position(event.position) {
                        anchor.set(Some(index));
                        selection.set((index, index));
                        ACTIVE_TEXT_SELECTION.store(selection_key, Ordering::Relaxed);
                        cx.stop_propagation();
                        window.refresh();
                    }
                }
            });
        }

        if is_selecting {
            let text_layout = self.layout.layout().clone();
            let selection_for_move = select_state.selection.clone();
            let anchor_for_move = select_state.anchor.clone();
            let hitbox_for_move = hitbox.clone();
            window.on_mouse_event(move |event: &gpui::MouseMoveEvent, phase, window, cx| {
                if phase == gpui::DispatchPhase::Bubble && let Some(start) = anchor_for_move.get() {
                    if hitbox_for_move.is_hovered(window) {
                        if let Ok(end) = text_layout.index_for_position(event.position) {
                            selection_for_move.set((start, end));
                        }
                        cx.stop_propagation();
                        window.refresh();
                    }
                }
            });

            let text_layout = self.layout.layout().clone();
            let selection_for_up = select_state.selection.clone();
            let anchor_for_up = select_state.anchor.clone();
            let hitbox_for_up = hitbox.clone();
            window.on_mouse_event(move |event: &gpui::MouseUpEvent, phase, window, cx| {
                if phase == gpui::DispatchPhase::Bubble && anchor_for_up.get().is_some() {
                    if hitbox_for_up.is_hovered(window) {
                        if let Ok(end) = text_layout.index_for_position(event.position) {
                            if let Some(start) = anchor_for_up.get() { selection_for_up.set((start, end)); }
                        }
                        cx.stop_propagation();
                        window.refresh();
                    }
                    anchor_for_up.set(None);
                }
            });
        }

        let (start, end) = select_state.selection.get();
        if ACTIVE_TEXT_SELECTION.load(Ordering::Relaxed) == self.selection_key && start != end {
            let min = start.min(end);
            let max = start.max(end);
            if let (Some(a), Some(b)) = (self.layout.layout().position_for_index(min), self.layout.layout().position_for_index(max)) {
                let left = a.x.min(b.x);
                let width = (a.x.max(b.x) - left).max(gpui::px(1.));
                let selection_bounds = Bounds::new(gpui::point(left, bounds.origin.y), gpui::size(width, bounds.size.height));
                window.paint_quad(gpui::fill(selection_bounds, rgb(0x4269a8)));
            }
            let text = self.text.clone();
            let selection_key = self.selection_key;
            window.on_key_event(move |event: &gpui::KeyDownEvent, phase, _window, cx| {
                if phase == gpui::DispatchPhase::Bubble && ACTIVE_TEXT_SELECTION.load(Ordering::Relaxed) == selection_key && event.keystroke.modifiers.platform && event.keystroke.key.eq_ignore_ascii_case("c") {
                    let from = min.min(text.len());
                    let to = max.min(text.len());
                    if text.is_char_boundary(from) && text.is_char_boundary(to) && from < to {
                        cx.write_to_clipboard(gpui::ClipboardItem::new_string(text[from..to].to_string()));
                        cx.stop_propagation();
                    }
                }
            });
        }
        self.layout.paint(id, inspector, bounds, state, &mut (), window, cx);
    }
}

fn selectable_text(text: impl Into<SharedString>, id: impl Into<ElementId>) -> SelectableText {
    SelectableText::new(text, id)
}

fn selectable_media_text(text: impl Into<SharedString>, path: &Path, field: &str) -> SelectableText {
    selectable_text(text, SharedString::from(format!("selectable-{}-{field}", path.display())))
}

#[derive(Clone, Copy, PartialEq)]
enum ViewMode {
    Names,
    Small,
    Large,
    Gallery,
}

#[derive(Clone, Copy, PartialEq)]
enum SortMode {
    CaptureDate,
    ImportDate,
    Filename,
}

struct PhotoApp {
    selected_section: String,
    diary_column_open: bool,
    diaries: Vec<DiaryEntry>,
    diary_trash: Vec<DiaryEntry>,
    diary_filter: String,
    selected_diary: Option<u64>,
    diary_editing: bool,
    diary_title_draft: String,
    diary_body_draft: String,
    diary_category_draft: String,
    diary_scroll: gpui::ScrollHandle,
    diary_title_edit: Option<gpui::Entity<DiaryTextField>>,
    diary_body_edit: Option<gpui::Entity<DiaryTextField>>,
    diary_photo_index: usize,
    diary_zoom_photo: Option<PathBuf>,
    diary_swipe_start: Option<gpui::Point<Pixels>>,
    diary_swipe_consumed: bool,
    diary_horizontal_scroll: f32,
    diary_horizontal_scroll_handled: bool,
    next_diary_id: u64,
    view_mode: ViewMode,
    categories: Vec<String>,
    category_items: HashMap<String, HashSet<PathBuf>>,
    category_removal_effect: Option<(f32, f32, u64)>,
    category_removal_effect_id: u64,
    photo_delete_flight: Option<(PathBuf, f32, f32, f32, f32, u64)>,
    photo_delete_flight_id: u64,
    last_selection_position: Option<(f32, f32)>,
    selected_media: usize,
    timeline_scroll: UniformListScrollHandle,
    active_timeline_year: Option<String>,
    notice: Option<String>,
    photos: Vec<PathBuf>,
    heic_previews: HashMap<PathBuf, PathBuf>,
    heic_preview_requests: HashSet<PathBuf>,
    heic_preview_failures: HashSet<PathBuf>,
    photo_thumbnails: HashMap<PathBuf, PathBuf>,
    photo_thumbnail_requests: HashSet<PathBuf>,
    photo_thumbnail_failures: HashSet<PathBuf>,
    duplicate_groups: Vec<Vec<PathBuf>>,
    duplicate_scan_running: bool,
    duplicate_scan_completed: bool,
    duplicate_selected: HashSet<PathBuf>,
    duplicate_keep_paths: HashMap<usize, PathBuf>,
    selected_paths: HashSet<PathBuf>,
    selection_anchor: Option<PathBuf>,
    selection_display_order: Vec<usize>,
    selection_box_start: Option<gpui::Point<gpui::Pixels>>,
    selection_box_rect: Option<(f32, f32, f32, f32)>,
    duplicate_scan_recursive: bool,
    duplicate_scope_menu_open: bool,
    capture_dates: HashMap<PathBuf, Option<String>>,
    capture_date_requests: HashSet<PathBuf>,
    capture_locations: HashMap<PathBuf, Option<String>>,
    image_dimensions: HashMap<PathBuf, Option<String>>,
    image_sizes: HashMap<PathBuf, (f32, f32)>,
    diary_capture_info: HashMap<PathBuf, Vec<String>>,
    image_dimensions_requests: HashSet<PathBuf>,
    source_directory: Option<PathBuf>,
    sort_mode: SortMode,
    sort_menu_open: bool,
    photo_context_menu: Option<PathBuf>,
    photo_context_menu_hovered: bool,
    pending_permanent_delete: Option<PathBuf>,
    gallery_list_width: f32,
    splitter_last_x: Option<f32>,
    diary_column_width: f32,
    diary_splitter_last_x: Option<f32>,
    connected_iphone: Option<String>,
    device_polling_started: bool,
    photo_save_directory: Option<PathBuf>,
    video_thumbnails: HashMap<PathBuf, PathBuf>,
    video_thumbnail_requests: HashSet<PathBuf>,
    video_thumbnail_failures: HashSet<PathBuf>,
    video_playback: Option<VideoPlayback>,
    video_controls_visible: bool,
    video_controls_last_motion: Option<std::time::Instant>,
    video_seeking: bool,
    photo_rotations: HashMap<PathBuf, u16>,
    rotated_photo_paths: HashMap<PathBuf, PathBuf>,
    photo_rotation_requests: HashSet<PathBuf>,
    photo_rotation_failures: HashSet<PathBuf>,
    list_name_width: f32,
    list_date_width: f32,
    list_size_width: f32,
    list_kind_width: f32,
    list_column_last_x: Option<f32>,
}

#[derive(Clone)]
struct DiaryEntry {
    id: u64,
    category: String,
    title: String,
    body: String,
    date: String,
    photos: Vec<PathBuf>,
}

actions!(diary_input, [DiaryBackspace, DiaryDelete, DiaryLeft, DiaryRight, DiarySelectLeft, DiarySelectRight, DiarySelectAll, DiaryPaste, DiaryCopy, DiaryCut]);

struct VideoPlayback {
    path: PathBuf,
    player: Retained<AVPlayer>,
    item: Retained<AVPlayerItem>,
    output: Retained<AVPlayerItemVideoOutput>,
    frame: Option<core_video::pixel_buffer::CVPixelBuffer>,
    playing: bool,
}
struct VideoSeekDrag { path: PathBuf }
struct ListColumnResizeDrag { column: usize }
struct YearTimelineDrag { targets: Vec<(String, String, usize)> }
struct MediaDragGhost { thumbnail: Option<PathBuf>, thumbnails: Vec<PathBuf>, width: f32, height: f32, show_removal_hint: bool, draw_offset: gpui::Point<gpui::Pixels> }
struct SelectionBoxDrag;
#[derive(Clone)]
struct MediaDrag { path: PathBuf, paths: Vec<PathBuf>, thumbnail: Option<PathBuf>, source_category: Option<String>, diary_source: Option<u64> }
#[derive(Clone)]
struct DiaryMediaReorderDrag { diary_id: u64, index: usize }
impl Render for MediaDragGhost {
    fn render(&mut self, _: &mut Window, _: &mut Context<Self>) -> impl IntoElement {
        let mut preview = div().flex().flex_col().items_center().gap_1();
        if self.show_removal_hint { preview = preview.child(div().px_2().py_1().rounded_full().bg(rgb(0x9d3f45)).text_xs().child("移出区域")); }
        if self.thumbnails.len() > 1 {
            let mut stack = div().relative().w(px(self.width + 24.)).h(px(self.height + 18.));
            for (index, path) in self.thumbnails.iter().enumerate() {
                stack = stack.child(img(path.clone()).absolute().left(px(index as f32 * 9.)).top(px((index as f32 - (self.thumbnails.len()-1) as f32 / 2.).abs() * 6.)).w(px(self.width)).h(px(self.height)).rounded_md().object_fit(ObjectFit::Contain));
            }
            preview = preview.child(stack);
        } else if let Some(path) = self.thumbnail.as_ref() {
            preview = preview.child(img(path.clone()).w(px(self.width)).h(px(self.height)).rounded_md().object_fit(ObjectFit::Contain));
        }
        preview
    }
}
impl Render for ListColumnResizeDrag { fn render(&mut self, _: &mut Window, _: &mut Context<Self>) -> impl IntoElement { div().size_0() } }
impl Render for VideoSeekDrag { fn render(&mut self, _: &mut Window, _: &mut Context<Self>) -> impl IntoElement { div().size_0() } }
impl Render for SelectionBoxDrag { fn render(&mut self, _: &mut Window, _: &mut Context<Self>) -> impl IntoElement { div().size_0() } }
impl Render for YearTimelineDrag { fn render(&mut self, _: &mut Window, _: &mut Context<Self>) -> impl IntoElement { div().size_0() } }

struct DiaryTextField {
    focus_handle: FocusHandle,
    content: SharedString,
    placeholder: SharedString,
    selected_range: Range<usize>,
    marked_range: Option<Range<usize>>,
    last_layout: Option<ShapedLine>,
    last_bounds: Option<Bounds<Pixels>>,
    multiline: bool,
}

impl DiaryTextField {
    fn safe_range(&self, range: Range<usize>) -> Range<usize> {
        let mut start = range.start.min(self.content.len());
        let mut end = range.end.min(self.content.len());
        while !self.content.is_char_boundary(start) { start -= 1; }
        while !self.content.is_char_boundary(end) { end -= 1; }
        if end < start { end = start; }
        start..end
    }
    fn offset_from_utf16(&self, offset: usize) -> usize {
        let mut utf8 = 0; let mut utf16 = 0;
        for ch in self.content.chars() { if utf16 >= offset { break; } utf8 += ch.len_utf8(); utf16 += ch.len_utf16(); }
        utf8
    }
    fn offset_to_utf16(&self, offset: usize) -> usize {
        let mut utf8 = 0; let mut utf16 = 0;
        for ch in self.content.chars() { if utf8 >= offset { break; } utf8 += ch.len_utf8(); utf16 += ch.len_utf16(); }
        utf16
    }
    fn inserted_offset_from_utf16(text: &str, offset: usize) -> usize {
        let mut bytes = 0;
        let mut units = 0;
        for ch in text.chars() {
            if units >= offset { break; }
            units += ch.len_utf16();
            bytes += ch.len_utf8();
        }
        bytes
    }
    fn range_from_utf16(&self, r: &Range<usize>) -> Range<usize> { self.offset_from_utf16(r.start)..self.offset_from_utf16(r.end) }
    fn range_to_utf16(&self, r: &Range<usize>) -> Range<usize> { self.offset_to_utf16(r.start)..self.offset_to_utf16(r.end) }
    fn replace(&mut self, range: Range<usize>, text: &str, cx: &mut Context<Self>) {
        let range = self.safe_range(range);
        self.content = format!("{}{}{}", &self.content[..range.start], text, &self.content[range.end..]).into();
        let p = range.start + text.len(); self.selected_range = p..p; self.marked_range = None; cx.notify();
    }
    fn backspace(&mut self, _: &DiaryBackspace, _: &mut Window, cx: &mut Context<Self>) {
        let mut r=self.selected_range.clone(); if r.is_empty() { r.start=self.content[..r.start].char_indices().last().map(|(i,_)|i).unwrap_or(0); } self.replace(r,"",cx);
    }
    fn delete(&mut self, _: &DiaryDelete, _: &mut Window, cx: &mut Context<Self>) {
        let mut r=self.selected_range.clone(); if r.is_empty() { r.end=self.content[r.end..].char_indices().nth(1).map(|(i,_)|r.end+i).unwrap_or(self.content.len()); } self.replace(r,"",cx);
    }
    fn left(&mut self, _: &DiaryLeft, _: &mut Window, cx: &mut Context<Self>) { let p=self.selected_range.start; let n=self.content[..p].char_indices().last().map(|(i,_)|i).unwrap_or(0); self.selected_range=n..n; cx.notify(); }
    fn right(&mut self, _: &DiaryRight, _: &mut Window, cx: &mut Context<Self>) { let p=self.selected_range.end; let n=self.content[p..].char_indices().nth(1).map(|(i,_)|p+i).unwrap_or(self.content.len()); self.selected_range=n..n; cx.notify(); }
    fn select_left(&mut self, _: &DiarySelectLeft, _: &mut Window, cx: &mut Context<Self>) { let p=self.selected_range.start; let n=self.content[..p].char_indices().last().map(|(i,_)|i).unwrap_or(0); self.selected_range=n..self.selected_range.end; cx.notify(); }
    fn select_right(&mut self, _: &DiarySelectRight, _: &mut Window, cx: &mut Context<Self>) { let p=self.selected_range.end; let n=self.content[p..].char_indices().nth(1).map(|(i,_)|p+i).unwrap_or(self.content.len()); self.selected_range=self.selected_range.start..n; cx.notify(); }
    fn select_all(&mut self, _: &DiarySelectAll, _: &mut Window, cx: &mut Context<Self>) { self.selected_range=0..self.content.len(); cx.notify(); }
    fn paste(&mut self, _: &DiaryPaste, _: &mut Window, cx: &mut Context<Self>) { if let Some(text)=cx.read_from_clipboard().and_then(|i|i.text()) { self.replace(self.selected_range.clone(), &text, cx); } }
    fn copy(&mut self, _: &DiaryCopy, _: &mut Window, cx: &mut Context<Self>) { if !self.selected_range.is_empty(){cx.write_to_clipboard(ClipboardItem::new_string(self.content[self.selected_range.clone()].to_string()));} }
    fn cut(&mut self, _: &DiaryCut, _: &mut Window, cx: &mut Context<Self>) { if !self.selected_range.is_empty(){cx.write_to_clipboard(ClipboardItem::new_string(self.content[self.selected_range.clone()].to_string())); self.replace(self.selected_range.clone(),"",cx);} }
}
impl EntityInputHandler for DiaryTextField {
    fn text_for_range(&mut self, r:Range<usize>, actual:&mut Option<Range<usize>>, _: &mut Window, _: &mut Context<Self>)->Option<String>{let r=self.range_from_utf16(&r);actual.replace(self.range_to_utf16(&r));Some(self.content[r].to_string())}
    fn selected_text_range(&mut self, _:bool,_:&mut Window,_:&mut Context<Self>)->Option<UTF16Selection>{Some(UTF16Selection{range:self.range_to_utf16(&self.selected_range),reversed:false})}
    fn marked_text_range(&self,_:&mut Window,_:&mut Context<Self>)->Option<Range<usize>>{self.marked_range.as_ref().map(|r|self.range_to_utf16(r))}
    fn unmark_text(&mut self,_:&mut Window,_:&mut Context<Self>){self.marked_range=None;}
    fn replace_text_in_range(&mut self,r:Option<Range<usize>>,text:&str,_:&mut Window,cx:&mut Context<Self>){let range=r.map(|r|self.range_from_utf16(&r)).or(self.marked_range.clone()).unwrap_or(self.selected_range.clone());self.replace(range,text,cx);}
    fn replace_and_mark_text_in_range(&mut self,r:Option<Range<usize>>,text:&str,new_sel:Option<Range<usize>>,_:&mut Window,cx:&mut Context<Self>){let range=self.safe_range(r.map(|r|self.range_from_utf16(&r)).or(self.marked_range.clone()).unwrap_or(self.selected_range.clone()));let start=range.start;self.content=format!("{}{}{}",&self.content[..range.start],text,&self.content[range.end..]).into();self.marked_range=(!text.is_empty()).then_some(start..start+text.len());let (selection_start,selection_end)=new_sel.map(|r|(Self::inserted_offset_from_utf16(text,r.start),Self::inserted_offset_from_utf16(text,r.end))).unwrap_or((text.len(),text.len()));self.selected_range=start+selection_start..start+selection_end;cx.notify();}
    fn bounds_for_range(&mut self,r:Range<usize>,bounds:Bounds<Pixels>,_:&mut Window,_:&mut Context<Self>)->Option<Bounds<Pixels>>{let line=self.last_layout.as_ref()?;let r=self.range_from_utf16(&r);Some(Bounds::from_corners(point(bounds.left()+line.x_for_index(r.start),bounds.top()),point(bounds.left()+line.x_for_index(r.end),bounds.bottom())))}
    fn character_index_for_point(&mut self,p:Point<Pixels>,_:&mut Window,_:&mut Context<Self>)->Option<usize>{let b=self.last_bounds?;let line=self.last_layout.as_ref()?;Some(self.offset_to_utf16(line.closest_index_for_x(p.x-b.left())))}
}

struct DiaryTextElement { input: Entity<DiaryTextField> }
struct DiaryTextPrepaint { line: ShapedLine, cursor: Option<PaintQuad>, selection: Option<PaintQuad> }
impl IntoElement for DiaryTextElement { type Element=Self; fn into_element(self)->Self{self} }
impl Element for DiaryTextElement {
    type RequestLayoutState=(); type PrepaintState=DiaryTextPrepaint;
    fn id(&self)->Option<ElementId>{None} fn source_location(&self)->Option<&'static core::panic::Location<'static>>{None}
    fn request_layout(&mut self,_:Option<&GlobalElementId>,_:Option<&InspectorElementId>,w:&mut Window,cx:&mut App)->(LayoutId,()){let mut s=Style::default();s.size.width=relative(1.).into();s.size.height=if self.input.read(cx).multiline{px(148.).into()}else{px(28.).into()};(w.request_layout(s,[],cx),())}
    fn prepaint(&mut self,_:Option<&GlobalElementId>,_:Option<&InspectorElementId>,b:Bounds<Pixels>,_:&mut (),w:&mut Window,cx:&mut App)->DiaryTextPrepaint{let i=self.input.read(cx);let text=if i.content.is_empty(){i.placeholder.clone()}else{i.content.clone()};let style=w.text_style();let color=if i.content.is_empty(){rgb(0x9699a1).into()}else{rgb(0xffffff).into()};let run=TextRun{len:text.len(),font:style.font(),color,background_color:None,underline:None,strikethrough:None};let line=w.text_system().shape_line(text,px(14.),&[run],None);let cursor_x=line.x_for_index(i.selected_range.end.min(i.content.len()));let cursor=Some(fill(Bounds::new(point(b.left()+cursor_x,b.top()),gpui::size(px(1.5),w.line_height())),rgb(0xd8c492)));let selection=if !i.selected_range.is_empty(){Some(fill(Bounds::from_corners(point(b.left()+line.x_for_index(i.selected_range.start),b.top()),point(b.left()+line.x_for_index(i.selected_range.end),b.bottom())),rgba(0x5577aaff)))}else{None};DiaryTextPrepaint{line,cursor,selection}}
    fn paint(&mut self,_:Option<&GlobalElementId>,_:Option<&InspectorElementId>,b:Bounds<Pixels>,_:&mut (),p:&mut DiaryTextPrepaint,w:&mut Window,cx:&mut App){let focus=self.input.read(cx).focus_handle.clone();w.handle_input(&focus,ElementInputHandler::new(b,self.input.clone()),cx);if let Some(q)=p.selection.take(){w.paint_quad(q)}p.line.paint(b.origin,w.line_height(),w,cx).ok();if focus.is_focused(w){if let Some(q)=p.cursor.take(){w.paint_quad(q)}}let line=p.line.clone();self.input.update(cx,|i,_|{i.last_layout=Some(line);i.last_bounds=Some(b);});}
}
impl Render for DiaryTextField { fn render(&mut self,_:&mut Window,cx:&mut Context<Self>)->impl IntoElement{let focus=self.focus_handle.clone();div().w_full().min_h(px(30.)).key_context("DiaryTextField").track_focus(&focus).cursor(CursorStyle::IBeam).on_action(cx.listener(Self::backspace)).on_action(cx.listener(Self::delete)).on_action(cx.listener(Self::left)).on_action(cx.listener(Self::right)).on_action(cx.listener(Self::select_left)).on_action(cx.listener(Self::select_right)).on_action(cx.listener(Self::select_all)).on_action(cx.listener(Self::paste)).on_action(cx.listener(Self::copy)).on_action(cx.listener(Self::cut)).on_mouse_down(MouseButton::Left,cx.listener(|this,e:&MouseDownEvent,window,cx|{window.focus(&this.focus_handle);let pos=e.position;let idx=this.last_bounds.zip(this.last_layout.as_ref()).map(|(b,l)|l.closest_index_for_x(pos.x-b.left())).unwrap_or(this.content.len()).min(this.content.len());let idx=if this.content.is_char_boundary(idx){idx}else{this.content.floor_char_boundary(idx)};this.selected_range=idx..idx;cx.notify();})).child(DiaryTextElement{input:cx.entity()})} }
impl Focusable for DiaryTextField { fn focus_handle(&self,_:&App)->FocusHandle{self.focus_handle.clone()} }

impl PhotoApp {
    fn diary_cached_image(&self, thumbnail: &Path) -> gpui::AnyElement {
        img(thumbnail.to_path_buf()).size_full().object_fit(ObjectFit::Contain)
            .with_fallback(image_error).into_any_element()
    }

    fn diary_media_preview(&mut self, source: &Path, cx: &mut Context<Self>) -> gpui::AnyElement {
        if is_supported_video(source) {
            if let Some(thumbnail) = self.video_thumbnail(source, cx) {
                return self.diary_cached_image(&thumbnail);
            }
            return if self.video_thumbnail_failures.contains(source) { image_error() }
                else { image_loading() };
        }
        if !is_supported_image(source) { return image_error(); }
        let display = self.photo_display_path(source, cx);
        img(display).size_full().object_fit(ObjectFit::Contain)
            .with_loading(|| image_loading()).with_fallback(|| image_error()).into_any_element()
    }

    fn diary_draggable_media(&mut self, source: &Path, diary_id: u64, cx: &mut Context<Self>) -> gpui::AnyElement {
        let preview = self.diary_media_preview(source, cx);
        let thumbnail = self.video_thumbnails.get(source)
            .or_else(|| self.photo_thumbnails.get(source))
            .or_else(|| self.heic_previews.get(source))
            .cloned()
            .or_else(|| {
                let cache = if is_supported_video(source) { video_thumbnail_cache_path(source) } else { photo_thumbnail_cache_path(source) };
                cache.filter(|path| path.is_file())
            })
            .unwrap_or_else(|| source.to_path_buf());
        let drag_path = source.to_path_buf();
        div().id(SharedString::from(format!("diary-photo-drag-{}-{}", diary_id, source.display())))
            .size_full().child(preview)
            .on_drag(
                MediaDrag {
                    path: drag_path.clone(),
                    paths: vec![drag_path],
                    thumbnail: Some(thumbnail),
                    source_category: None,
                    diary_source: Some(diary_id),
                },
                |drag, cursor_offset, _, cx| {
                    let thumbnail = drag.thumbnail.clone();
                    let preview_path = thumbnail.clone().unwrap_or_else(|| drag.path.clone());
                    let (width, height) = thumbnail_dimensions(&preview_path);
                    let width = width.clamp(72., 180.);
                    let height = height.clamp(56., 150.);
                    let draw_offset = point(cursor_offset.x - px(width / 2.), cursor_offset.y - px(height / 2.));
                    cx.new(move |_| MediaDragGhost {
                        thumbnail,
                        thumbnails: Vec::new(),
                        width,
                        height,
                        show_removal_hint: false,
                        draw_offset,
                    })
                },
            )
            .into_any_element()
    }

    fn render_diary_column(&mut self, window_height: f32, cx: &mut Context<Self>) -> impl IntoElement {
        let categories = ["全部", "日常", "旅行", "美食", "家人", "随想"];
        let selected_entry = self.selected_diary.and_then(|id| self.diaries.iter().find(|entry| entry.id == id)).cloned();
        let mut column = div().id("diary-column").relative().w(px(self.diary_column_width)).min_w(px(0.)).h_full().flex().flex_col()
            .border_l_1().border_color(rgb(0x3b3d41)).bg(rgb(0x252628))
            .on_click(cx.listener(|_, _, _, cx| cx.stop_propagation()));
        let mut list_column = div().id("diary-list-column").flex_1().min_h(px(0.)).h_full().flex().flex_col();
        let header = div().flex().items_center().justify_between().px_4().py_4().border_b_1().border_color(rgb(0x3b3d41))
            .child(div().flex().flex_col().gap_1()
                .child(div().text_lg().font_weight(gpui::FontWeight::SEMIBOLD).text_color(rgb(0xf2f0ec)).child(format!("日记  {} 篇", self.diaries.len())))
                .child(div().text_xs().text_color(rgb(0x92949a)).child("照片库 · 日记栏（第三栏）")))
            .child(div().flex().items_center().gap_2()
                .child(button("＋ 新增", true).on_click(cx.listener(|this, _, _, cx| this.start_new_diary(cx))))
                .child(button("×", false).on_click(cx.listener(|this, _, _, cx| this.close_diary_column(cx)))));
        list_column = list_column.child(header);
        let mut filters = div().id("diary-filters").flex().gap_2().overflow_x_scroll().px_3().py_3().border_b_1().border_color(rgb(0x393b3f));
        for category in categories {
            let active = self.diary_filter == category;
            let label = category.to_string();
            filters = filters.child(button(label.clone(), active).rounded_full().on_click(cx.listener(move |this, _, _, cx| {
                this.diary_filter = label.clone(); this.selected_diary = None; this.diary_editing = false; cx.notify();
            })));
        }
        list_column = list_column.child(filters);

        let mut list = div().id("diary-list").flex_1().min_w(px(0.)).overflow_y_scroll().flex().flex_col().gap_2().p_3()
            .track_scroll(&self.diary_scroll);
        let visible: Vec<DiaryEntry> = self.diaries.iter().filter(|entry| self.diary_filter == "全部" || entry.category == self.diary_filter).cloned().collect();
        let wide_diary_layout = self.diary_column_width >= 470.;
        let mut list_timeline_targets = Vec::<(String, usize)>::new();
        let mut seen_years = HashSet::new();
        for (index, entry) in visible.iter().enumerate() {
            let year = entry.date.get(0..4).filter(|year| year.chars().all(|c| c.is_ascii_digit())).unwrap_or("未知").to_string();
            if seen_years.insert(year.clone()) { list_timeline_targets.push((year, index)); }
        }
        if visible.is_empty() {
            list = list.child(div().p_4().text_sm().text_color(rgb(0x92949a)).child("这里还没有日记。点击“新增日记”开始记录。"));
        }
        if !wide_diary_layout {
        let list_text_width = (self.diary_column_width - 194.).max(40.);
        for entry in visible.iter().cloned() {
            let active = self.selected_diary == Some(entry.id);
            let entry_id = entry.id;
            let mut card = div().id(SharedString::from(format!("diary-entry-{entry_id}"))).w_full().min_w(px(0.)).overflow_hidden().flex().gap_3().p_2().rounded_lg()
                .border_1().border_color(if active { rgb(0x55575c) } else { rgb(0x252628) })
                .bg(if active { rgb(0x303236) } else { rgb(0x252628) })
                .cursor_pointer().on_click(cx.listener(move |this, _, _, cx| {
                    this.selected_diary = Some(entry_id); this.diary_editing = false; this.diary_photo_index = 0; cx.notify();
                }))
                .drag_over::<MediaDrag>(|style, _, _, _| style.bg(rgb(0x38352c)).border_1().border_color(rgb(0xd9c68f)))
                .on_drop(cx.listener(move |this, drag: &MediaDrag, window, cx| {
                    let point = window.mouse_position();
                    let position = (point.x.to_f64() as f32, point.y.to_f64() as f32);
                    if this.add_media_to_diary(entry_id, &drag.paths, cx) > 0 {
                        this.trigger_diary_media_flight(&drag.path, position, cx);
                    }
                }));
            if let Some(photo) = entry.photos.first() {
                card = card.child(div().w(px(78.)).h(px(72.)).flex_none().rounded_md().overflow_hidden()
                    .child(self.diary_draggable_media(photo, entry_id, cx)));
            } else {
                card = card.child(div().w(px(78.)).h(px(72.)).flex_none().rounded_md().bg(rgb(0x33363a)).flex().items_center().justify_center().text_xl().text_color(rgb(0x777a80)).child("▧"));
            }
            let title = if entry.title.is_empty() { "无标题日记" } else { &entry.title };
            let snippet = entry.body.lines().next().unwrap_or("还没有写内容");
            let title = truncate_diary_preview(title, list_text_width, 14.);
            let metadata = truncate_diary_preview(&format!("{} · {}", entry.category, entry.date), list_text_width, 12.);
            let snippet = truncate_diary_preview(snippet, list_text_width, 12.);
            card = card.child(div().w(px(list_text_width)).flex_none().min_w(px(0.)).overflow_hidden().flex().flex_col().justify_center().gap_1()
                .child(div().w_full().min_w(px(0.)).overflow_hidden().text_sm().font_weight(gpui::FontWeight::BOLD).text_color(rgb(0xffffff)).child(title))
                .child(div().w_full().min_w(px(0.)).overflow_hidden().text_xs().text_color(rgb(0x96989e)).child(metadata))
                .child(div().w_full().min_w(px(0.)).overflow_hidden().text_xs().text_color(rgb(0xb2b3b7)).child(snippet)));
            list = list.child(card);
        }
        }
        if let Some(entry) = selected_entry {
            let mut detail = div().id("diary-detail").flex_1().min_h(px(0.)).h_full().flex().flex_col().bg(rgb(0x252628));
            let top = div().flex().items_center().justify_between().px_4().py_3().border_b_1().border_color(rgb(0x393b3f))
                .child(button("‹  日记列表", false).on_click(cx.listener(|this, _, _, cx| { this.selected_diary = None; this.diary_editing = false; cx.notify(); })))
                .child(button("×", false).on_click(cx.listener(|this, _, _, cx| { this.selected_diary = None; cx.notify(); })));
            detail = detail.child(top);
            if self.diary_editing {
                let mut category_choices = div().flex().gap_2();
                for category in ["日常", "旅行", "美食", "家人", "随想"] {
                    let selected = self.diary_category_draft == category;
                    let value = category.to_string();
                    category_choices = category_choices.child(button(value.clone(), selected).rounded_full().on_click(cx.listener(move |this, _, _, cx| {
                        this.diary_category_draft = value.clone();
                        cx.notify();
                    })));
                }
                let mut attached_media = div().id("diary-edit-attached-media").w_full().flex().gap_2().overflow_x_scroll();
                for (media_index, media_path) in entry.photos.iter().enumerate() {
                    let is_video = is_supported_video(media_path);
                    let diary_id = entry.id;
                    let source = media_path.clone();
                    let preview = self.diary_media_preview(media_path, cx);
                    let current_rotation = self.photo_rotations.get(media_path).copied().unwrap_or(0);
                    let drag_thumbnail = self.video_thumbnails.get(media_path)
                        .or_else(|| self.photo_thumbnails.get(media_path))
                        .or_else(|| self.heic_previews.get(media_path))
                        .cloned()
                        .or_else(|| {
                            let cache = if is_video { video_thumbnail_cache_path(media_path) }
                                else { photo_thumbnail_cache_path_for_rotation(media_path, current_rotation) };
                            cache.filter(|path| path.is_file())
                        })
                        .unwrap_or_else(|| source.clone());
                    let mut thumbnail = div().id(SharedString::from(format!("diary-edit-media-{media_index}")))
                        .relative().w(px(84.)).h(px(68.)).flex_none().rounded_md().overflow_hidden().bg(rgb(0x33363a))
                        .child(preview)
                        .on_drag(DiaryMediaReorderDrag { diary_id, index: media_index }, move |_, cursor_offset, _, cx| {
                            let thumbnail = drag_thumbnail.clone();
                            let (width, height) = thumbnail_dimensions(&thumbnail);
                            let draw_offset = point(cursor_offset.x - px(width / 2.), cursor_offset.y - px(height / 2.));
                            cx.new(move |_| MediaDragGhost {
                                thumbnail: Some(thumbnail), thumbnails: Vec::new(), width, height,
                                show_removal_hint: false, draw_offset,
                            })
                        })
                        .drag_over::<DiaryMediaReorderDrag>(|style, _, _, _| style.border_2().border_color(rgb(0xd9c68f)).bg(rgb(0x38352c)))
                        .on_drop(cx.listener(move |this, drag: &DiaryMediaReorderDrag, _, cx| {
                            if drag.diary_id == diary_id {
                                this.reorder_diary_media(diary_id, drag.index, media_index, cx);
                            }
                            cx.stop_propagation();
                        }))
                        .drag_over::<MediaDrag>(|style, _, _, _| style.border_2().border_color(rgb(0x88a9ff)).bg(rgb(0x30343b)))
                        .on_drop(cx.listener(move |this, drag: &MediaDrag, window, cx| {
                            let point = window.mouse_position();
                            let position = (point.x.to_f64() as f32, point.y.to_f64() as f32);
                            if this.insert_media_into_diary(diary_id, &drag.paths, media_index, cx) > 0 {
                                this.trigger_diary_media_flight(&drag.path, position, cx);
                            }
                            cx.stop_propagation();
                        }));
                    if is_video {
                        thumbnail = thumbnail.child(div().absolute().right(px(4.)).bottom(px(4.)).px_1().rounded_sm()
                            .bg(rgba(0x17181acc)).text_xs().text_color(rgb(0xffffff)).child("▶"));
                    }
                    attached_media = attached_media.child(thumbnail);
                }
                if entry.photos.is_empty() {
                    attached_media = attached_media.child(div().w(px(84.)).h(px(68.)).flex_none().rounded_md().bg(rgb(0x202124))
                        .flex().items_center().justify_center().text_xs().text_color(rgb(0x777a80)).child("暂无媒体"));
                }
                detail = detail.child(div().id("diary-edit-scroll").flex_1().overflow_y_scroll().flex().flex_col().gap_3().p_4()
                    .drag_over::<MediaDrag>(|style, _, _, _| style.bg(rgb(0x302f2b)).border_1().border_color(rgb(0xd9c68f)))
                    .on_drop(cx.listener(|this, drag: &MediaDrag, _, cx| this.add_photos_to_diary(&drag.paths, cx)))
                    .child(div().text_xs().text_color(rgb(0xddc995)).child("编辑日记"))
                    .child(div().text_xs().text_color(rgb(0xa7abb4)).child("主题分类"))
                    .child(category_choices)
                    .child(div().w_full().px_3().py_2().rounded_md().border_1().border_color(rgb(0x44464a)).bg(rgb(0x202124))
                        .child(self.diary_title_edit.get_or_insert_with(|| cx.new(|cx| DiaryTextField { focus_handle: cx.focus_handle(), content: self.diary_title_draft.clone().into(), placeholder: "日记标题".into(), selected_range: 0..self.diary_title_draft.len(), marked_range: None, last_layout: None, last_bounds: None, multiline: false })).clone()))
                    .child(div().w_full().min_h(px(150.)).px_3().py_2().rounded_md().border_1().border_color(rgb(0x44464a)).bg(rgb(0x202124))
                        .child(self.diary_body_edit.get_or_insert_with(|| cx.new(|cx| DiaryTextField { focus_handle: cx.focus_handle(), content: self.diary_body_draft.clone().into(), placeholder: "写下今天的故事…".into(), selected_range: 0..self.diary_body_draft.len(), marked_range: None, last_layout: None, last_bounds: None, multiline: true })).clone()))
                    .child(div().text_xs().text_color(rgb(0xa7abb4)).child(format!("已添加 {} 个媒体", entry.photos.len())))
                    .child(attached_media)
                    .child(div().p_3().border_1().border_color(rgb(0x60636a)).rounded_md().text_xs().text_color(rgb(0xa7abb4)).child("拖动缩略图调整顺序 · 拖入照片或视频添加到日记"))
                    .child(div().flex().gap_2()
                        .child(button("保存修改", true).on_click(cx.listener(|this, _, _, cx| this.save_diary_draft(cx))))
                        .child(button("取消", false).on_click(cx.listener(|this, _, _, cx| { this.diary_editing = false; this.diary_title_edit = None; this.diary_body_edit = None; cx.notify(); })))))
            } else {
                let mut body = div().id("diary-body-scroll").flex_1().overflow_y_scroll().p_4().flex().flex_col().gap_3()
                    .child(div().text_xs().text_color(rgb(0xddc995)).child(format!("{} · 日记", entry.category)))
                    .child(div().text_2xl().font_weight(gpui::FontWeight::BOLD).text_color(rgb(0xffffff)).child(if entry.title.is_empty() { "无标题日记".to_string() } else { entry.title.clone() }))
                    .child(div().text_sm().text_color(rgb(0x96989e)).child(format!("{} · {} 个媒体", entry.date, entry.photos.len())))
                    .child(div().text_base().text_color(rgb(0xd0d0ce)).child(if entry.body.is_empty() { "还没有写内容".to_string() } else { entry.body.clone() }));
                if let Some(photo) = entry.photos.get(self.diary_photo_index).or_else(|| entry.photos.first()) {
                    let index = self.diary_photo_index;
                    let is_video = is_supported_video(photo);
                    let (mut image_width, mut image_height) = if is_video {
                        self.video_thumbnail(photo, cx).map(|thumbnail| thumbnail_dimensions(&thumbnail)).unwrap_or((16., 9.))
                    } else {
                        self.request_image_dimensions(photo, cx);
                        self.image_sizes.get(photo).copied().unwrap_or((4., 3.))
                    };
                    if !is_video && self.photo_rotations.get(photo).is_some_and(|degrees| degrees % 180 != 0) {
                        std::mem::swap(&mut image_width, &mut image_height);
                    }
                    let available_width = (self.diary_column_width - 32.).max(180.);
                    let available_height = (window_height * 0.58).max(180.);
                    let scale = (available_width / image_width.max(1.)).min(available_height / image_height.max(1.));
                    let display_width = (image_width * scale).max(1.);
                    let display_height = (image_height * scale).max(1.);
                    let photo_path = photo.clone();
                    let photo_count = entry.photos.len();
                    let diary_id = entry.id;
                    let mut carousel = div().relative().w_full().h(px(display_height)).flex_none().flex().justify_center().rounded_lg().overflow_hidden().bg(rgb(0x303236))
                        .drag_over::<MediaDrag>(|style, _, _, _| style.border_2().border_color(rgb(0xd9c68f)).bg(rgb(0x38352c)))
                        .on_drop(cx.listener(move |this, drag: &MediaDrag, window, cx| {
                            let point = window.mouse_position();
                            let position = (point.x.to_f64() as f32, point.y.to_f64() as f32);
                            if this.add_media_to_diary(diary_id, &drag.paths, cx) > 0 {
                                this.trigger_diary_media_flight(&drag.path, position, cx);
                            }
                        }))
                        .on_mouse_down(gpui::MouseButton::Left, cx.listener(|this, event: &gpui::MouseDownEvent, _, _| {
                            this.diary_swipe_consumed = false;
                            this.diary_swipe_start = Some(event.position);
                        }))
                        .on_mouse_up(gpui::MouseButton::Left, cx.listener(move |this, event: &gpui::MouseUpEvent, _, cx| {
                            let Some(start) = this.diary_swipe_start.take() else { return; };
                            let dx = (event.position.x - start.x).to_f64() as f32;
                            let dy = (event.position.y - start.y).to_f64() as f32;
                            if dx.abs() > 60. && dx.abs() > dy.abs() * 1.2 && photo_count > 1 {
                                this.diary_swipe_consumed = true;
                                let count = photo_count;
                                this.diary_photo_index = if dx < 0. {
                                    (this.diary_photo_index + 1) % count
                                } else {
                                    (this.diary_photo_index + count - 1) % count
                                };
                                cx.stop_propagation();
                                cx.notify();
                            }
                        }))
                        .on_scroll_wheel(cx.listener(move |this, event: &gpui::ScrollWheelEvent, _, cx| {
                            if matches!(event.touch_phase, gpui::TouchPhase::Started) {
                                this.diary_horizontal_scroll = 0.;
                                this.diary_horizontal_scroll_handled = false;
                            }
                            if matches!(event.touch_phase, gpui::TouchPhase::Ended) {
                                this.diary_horizontal_scroll = 0.;
                                this.diary_horizontal_scroll_handled = false;
                                return;
                            }
                            if this.diary_horizontal_scroll_handled { return; }
                            if photo_count < 2 { return; }
                            let delta = event.delta.pixel_delta(px(40.));
                            let dx = delta.x.to_f64() as f32;
                            let dy = delta.y.to_f64() as f32;
                            // Only treat a clearly horizontal trackpad/mouse gesture as a photo swipe.
                            if dx.abs() <= dy.abs() * 1.25 { return; }
                            this.diary_horizontal_scroll += dx;
                            if this.diary_horizontal_scroll.abs() >= 50. {
                                let count = photo_count;
                                this.diary_photo_index = if this.diary_horizontal_scroll < 0. {
                                    (this.diary_photo_index + 1) % count
                                } else {
                                    (this.diary_photo_index + count - 1) % count
                                };
                                this.diary_horizontal_scroll = 0.;
                                // A trackpad swipe emits multiple scroll events. Consume only
                                // one photo change until that gesture reports its end.
                                this.diary_horizontal_scroll_handled = true;
                                cx.stop_propagation();
                                cx.notify();
                            }
                        }))
                        .child({
                            let mut target = div().id(SharedString::from(format!("diary-zoom-target-{}-{}", entry.id, index)))
                                .relative().w(px(display_width)).h(px(display_height))
                                .child(self.diary_draggable_media(photo, entry.id, cx));
                            if !is_video {
                                target = target.cursor_pointer().on_click(cx.listener(move |this, _, _, cx| {
                                    if this.diary_swipe_consumed { this.diary_swipe_consumed = false; cx.stop_propagation(); return; }
                                    this.diary_zoom_photo = Some(photo_path.clone()); cx.notify();
                                }));
                            }
                            target
                        });
                    if is_video {
                        let play_path = photo.clone();
                        carousel = carousel.child(button("▶ 播放视频", false).absolute().bottom(px(10.)).right(px(10.))
                            .bg(rgba(0x202124b0)).hover(|style| style.bg(rgba(0x202124e8)))
                            .on_click(cx.listener(move |this, _, _, cx| { cx.stop_propagation(); this.open_media(play_path.clone(), cx); })));
                    }
                    if is_supported_image(photo) {
                        if let Some(live_movie) = live_photo_movie(photo) {
                            carousel = carousel.child(button("LIVE ▶", false)
                                .absolute().top(px(8.)).left(px(8.))
                                .bg(rgba(0x17181ad0)).text_color(rgb(0xffffff))
                                .hover(|style| style.bg(rgba(0x17181af0)))
                                .on_click(cx.listener(move |this, _, _, cx| {
                                    cx.stop_propagation();
                                    this.open_media(live_movie.clone(), cx);
                                })));
                        }
                        let rotate_path = photo.clone();
                        carousel = carousel.child(
                            button("↻ 旋转", false)
                                .absolute().top(px(8.)).right(px(8.))
                                .bg(rgba(0x292a2d90))
                                .hover(|style| style.bg(rgba(0x292a2de0)))
                                .on_click(cx.listener(move |this, _, _, cx| { cx.stop_propagation(); this.rotate_photo(rotate_path.clone(), cx); })),
                        );
                    }
                    if entry.photos.len() > 1 {
                        carousel = carousel.child(div().absolute().left(px(8.)).right(px(8.)).top(px(108.)).flex().justify_between()
                            .child(button("‹", false).on_click(cx.listener(|this, _, _, cx| {
                                cx.stop_propagation();
                                let count = this.selected_diary.and_then(|id| this.diaries.iter().find(|e| e.id == id)).map(|e| e.photos.len()).unwrap_or(1);
                                this.diary_photo_index = (this.diary_photo_index + count - 1) % count; cx.notify();
                            })))
                            .child(button("›", false).on_click(cx.listener(|this, _, _, cx| {
                                cx.stop_propagation();
                                let count = this.selected_diary.and_then(|id| this.diaries.iter().find(|e| e.id == id)).map(|e| e.photos.len()).unwrap_or(1);
                                this.diary_photo_index = (this.diary_photo_index + 1) % count; cx.notify();
                            }))));
                    }
                    body = body.child(carousel).child(div().text_xs().text_color(rgb(0xc6c8cc)).text_center().child(format!("{} / {}", index + 1, entry.photos.len())));
                    if !is_video {
                        let capture_info = self.diary_capture_info.entry(photo.clone())
                            .or_insert_with(|| diary_photo_capture_info(photo)).clone();
                        body = body.child(div().w_full().px_2().flex().flex_col().gap_1()
                            .children(capture_info.into_iter().map(|line| {
                                div().text_xs().text_color(rgb(0x96989e)).child(line)
                            })));
                    }
                }
                body = body.child(div().p_3().border_1().border_color(rgb(0x60636a)).rounded_md().text_xs().text_color(rgb(0xa7abb4))
                    .child("拖入照片或视频添加到日记")
                    .drag_over::<MediaDrag>(|style, _, _, _| style.bg(rgb(0x38352c)).border_color(rgb(0xd9c68f)))
                    .on_drop(cx.listener(|this, drag: &MediaDrag, _, cx| this.add_photos_to_diary(&drag.paths, cx))))
                    .child(div().flex().gap_2()
                        .child(button("编辑日记", false).on_click(cx.listener(|this, _, _, cx| {
                            if let Some(entry) = this.selected_diary.and_then(|id| this.diaries.iter().find(|entry| entry.id == id)) {
                                this.diary_title_draft = entry.title.clone(); this.diary_body_draft = entry.body.clone(); this.diary_category_draft = entry.category.clone(); this.diary_title_edit = None; this.diary_body_edit = None;
                            }
                            this.diary_editing = true; cx.notify();
                        })))
                        .child(button("删除日记", false).on_click(cx.listener(|this, _, _, cx| this.delete_selected_diary(cx)))));
                detail = detail.child(body);
            }
            column = column.child(detail);
        } else {
            if wide_diary_layout {
                let mut by_year = BTreeMap::<String, Vec<DiaryEntry>>::new();
                for entry in visible.iter().cloned() {
                    let year = entry.date.get(0..4).filter(|year| year.chars().all(|c| c.is_ascii_digit())).unwrap_or("未知").to_string();
                    by_year.entry(year).or_default().push(entry);
                }
                let year_groups: Vec<(String, Vec<DiaryEntry>)> = by_year.into_iter().rev().collect();
                let inner_width = (self.diary_column_width - 92.).max(160.);
                let columns = ((inner_width + 12.) / 172.).floor().max(1.) as usize;
                let tile_width = ((inner_width - 12. * columns.saturating_sub(1) as f32) / columns as f32).max(130.);
                let mut timeline = div().id("diary-time-axis").w(px(68.)).flex_none().h_full().flex().flex_col().gap_2().p_2()
                    .border_r_1().border_color(rgb(0x393b3f));
                for (group_index, (year, _entries)) in year_groups.iter().enumerate() {
                    let label = if year == "未知" { "未知".to_string() } else { year.clone() };
                    timeline = timeline.child(button(label, false).w_full().text_xs().whitespace_nowrap().text_ellipsis().on_click(cx.listener(move |this, _, _, cx| {
                        this.diary_scroll.scroll_to_top_of_item(group_index);
                        cx.notify();
                    })));
                }
                let mut tile_scroll = div().id("diary-tile-scroll").flex_1().min_w(px(0.)).h_full().overflow_y_scroll().flex().flex_col().gap_3().p_3()
                    .track_scroll(&self.diary_scroll);
                for (year, entries) in year_groups {
                    let mut year_section = div().id(SharedString::from(format!("diary-year-{year}"))).flex().flex_col().gap_2()
                        .child(div().text_sm().font_weight(gpui::FontWeight::SEMIBOLD).text_color(rgb(0xd8c58f))
                            .child(if year == "未知" { "日期未知".to_string() } else { format!("{year} 年") }));
                    for chunk in entries.chunks(columns) {
                        let mut row = div().flex().gap_3();
                        for entry in chunk {
                            let entry_id = entry.id;
                            let title = if entry.title.is_empty() { "无标题日记" } else { &entry.title };
                            let snippet = entry.body.lines().next().unwrap_or("还没有写内容");
                            let content_width = (tile_width - 16.).max(40.);
                            let title = truncate_diary_preview(title, content_width, 14.);
                            let metadata = truncate_diary_preview(&format!("{} · {}", entry.category, entry.date), content_width, 12.);
                            let snippet = truncate_diary_preview(snippet, content_width, 12.);
                            let mut tile = div().id(SharedString::from(format!("diary-tile-{entry_id}"))).w(px(tile_width)).flex_none().flex().flex_col().gap_2().p_2()
                                .rounded_lg().border_1().border_color(if self.selected_diary == Some(entry_id) { rgb(0x55575c) } else { rgb(0x393b3f) })
                                .bg(rgb(0x2b2d30)).cursor_pointer().on_click(cx.listener(move |this, _, _, cx| {
                                    this.selected_diary = Some(entry_id); this.diary_editing = false; this.diary_photo_index = 0; cx.notify();
                                }))
                                .drag_over::<MediaDrag>(|style, _, _, _| style.bg(rgb(0x38352c)).border_2().border_color(rgb(0xd9c68f)))
                                .on_drop(cx.listener(move |this, drag: &MediaDrag, window, cx| {
                                    let point = window.mouse_position();
                                    let position = (point.x.to_f64() as f32, point.y.to_f64() as f32);
                                    if this.add_media_to_diary(entry_id, &drag.paths, cx) > 0 {
                                        this.trigger_diary_media_flight(&drag.path, position, cx);
                                    }
                                }));
                            if let Some(photo) = entry.photos.first() {
                                tile = tile.child(div().w_full().h(px(tile_width * 0.62)).rounded_md().overflow_hidden().bg(rgb(0x33363a))
                                    .child(self.diary_draggable_media(photo, entry_id, cx)));
                            } else {
                                tile = tile.child(div().w_full().h(px(tile_width * 0.62)).rounded_md().bg(rgb(0x33363a)).flex().items_center().justify_center()
                                    .text_2xl().text_color(rgb(0x777a80)).child("▧"));
                            }
                            tile = tile.child(div().w_full().min_w(px(0.)).overflow_hidden().text_sm().font_weight(gpui::FontWeight::BOLD).text_color(rgb(0xffffff)).child(title))
                                .child(div().w_full().min_w(px(0.)).overflow_hidden().text_xs().text_color(rgb(0x96989e)).child(metadata))
                                .child(div().w_full().min_w(px(0.)).overflow_hidden().text_xs().text_color(rgb(0xb2b3b7)).child(snippet));
                            row = row.child(tile);
                        }
                        year_section = year_section.child(row);
                    }
                    tile_scroll = tile_scroll.child(year_section);
                }
                if visible.is_empty() {
                    tile_scroll = tile_scroll.child(div().p_4().text_sm().text_color(rgb(0x92949a)).child("这里还没有日记。点击“新增日记”开始记录。"));
                }
                list_column = list_column.child(div().flex_1().min_h(px(0.)).flex().child(timeline).child(tile_scroll));
            } else {
                let mut timeline = div().id("diary-list-time-axis").w(px(64.)).flex_none().h_full().flex().flex_col().gap_2().p_2()
                    .border_r_1().border_color(rgb(0x393b3f));
                for (year, target_index) in list_timeline_targets {
                    let label = if year == "未知" { "未知".to_string() } else { year.clone() };
                    timeline = timeline.child(button(label, false).w_full().text_xs().whitespace_nowrap().text_ellipsis().on_click(cx.listener(move |this, _, _, cx| {
                        this.diary_scroll.scroll_to_top_of_item(target_index);
                        cx.notify();
                    })));
                }
                list_column = list_column.child(div().flex_1().min_w(px(0.)).min_h(px(0.)).flex().child(timeline).child(list));
            }
            column = column.child(list_column);
        }
        column
    }

    fn save_diary_data(&mut self, cx: &mut Context<Self>) {
        if let Err(error) = save_diaries(&self.diaries) { self.notice = Some(format!("日记保存失败：{error}")); }
        cx.notify();
    }

    fn start_new_diary(&mut self, cx: &mut Context<Self>) {
        let id = self.next_diary_id;
        self.next_diary_id = self.next_diary_id.saturating_add(1);
        let date = chrono_free_date();
        let category = if self.diary_filter == "全部" { "日常".to_string() } else { self.diary_filter.clone() };
        self.diary_category_draft = category.clone();
        self.diaries.insert(0, DiaryEntry { id, category, title: String::new(), body: String::new(), date, photos: Vec::new() });
        self.selected_diary = Some(id);
        self.diary_editing = true;
        self.diary_title_draft.clear();
        self.diary_body_draft.clear();
        self.diary_title_edit = None;
        self.diary_body_edit = None;
        self.diary_photo_index = 0;
        let _ = save_diaries(&self.diaries);
        self.set_section("日记", cx);
    }

    fn add_photos_to_diary(&mut self, paths: &[PathBuf], cx: &mut Context<Self>) {
        let Some(id) = self.selected_diary else { self.notice = Some("先选择或新建一篇日记，再拖入照片或视频。".into()); cx.notify(); return; };
        let _ = self.add_media_to_diary(id, paths, cx);
    }

    fn add_media_to_diary(&mut self, id: u64, paths: &[PathBuf], cx: &mut Context<Self>) -> usize {
        let mut added = 0;
        if let Some(entry) = self.diaries.iter_mut().find(|entry| entry.id == id) {
            for path in paths {
                if is_supported_media(path) && self.photos.iter().any(|photo| photo == path) && !entry.photos.contains(path) {
                    entry.photos.push(path.clone()); added += 1;
                }
            }
            if self.selected_diary == Some(id) && added > 0 {
                self.diary_photo_index = entry.photos.len().saturating_sub(1);
            }
        }
        self.notice = Some(if added > 0 {
            format!("已将 {added} 个照片或视频加入日记。")
        } else {
            "这些媒体已在日记中，或不属于当前图库。".into()
        });
        let _ = save_diaries(&self.diaries);
        cx.notify();
        added
    }

    fn insert_media_into_diary(&mut self, id: u64, paths: &[PathBuf], index: usize, cx: &mut Context<Self>) -> usize {
        let mut added = 0;
        if let Some(entry) = self.diaries.iter_mut().find(|entry| entry.id == id) {
            let mut insert_at = index.min(entry.photos.len());
            for path in paths {
                if is_supported_media(path)
                    && self.photos.iter().any(|photo| photo == path)
                    && !entry.photos.contains(path)
                {
                    entry.photos.insert(insert_at, path.clone());
                    insert_at += 1;
                    added += 1;
                }
            }
            if self.selected_diary == Some(id) && added > 0 {
                self.diary_photo_index = index.min(entry.photos.len().saturating_sub(1));
            }
        }
        self.notice = Some(if added > 0 {
            format!("已在第 {} 个位置插入 {added} 个媒体。", index + 1)
        } else {
            "这些媒体已在日记中，或不属于当前图库。".into()
        });
        let _ = save_diaries(&self.diaries);
        cx.notify();
        added
    }

    fn trigger_diary_media_flight(&mut self, path: &Path, position: (f32, f32), cx: &mut Context<Self>) {
        if let Some(thumbnail) = self.prepare_delete_flight_thumbnail(path) {
            let destination = (position.0 - 42., position.1 - 28.);
            self.trigger_photo_flight_to(thumbnail, position, destination, cx);
        }
    }

    fn remove_photos_from_diary(&mut self, diary_id: u64, paths: &[PathBuf], cx: &mut Context<Self>) {
        let mut removed = 0;
        if let Some(entry) = self.diaries.iter_mut().find(|entry| entry.id == diary_id) {
            let before = entry.photos.len();
            entry.photos.retain(|photo| !paths.contains(photo));
            removed = before - entry.photos.len();
            self.diary_photo_index = self.diary_photo_index.min(entry.photos.len().saturating_sub(1));
        }
        if removed > 0 {
            self.notice = Some(format!("已将 {removed} 个媒体移出日记。媒体仍保留在照片库中。"));
            self.save_diary_data(cx);
        } else {
            cx.notify();
        }
    }

    fn reorder_diary_media(&mut self, diary_id: u64, from: usize, to: usize, cx: &mut Context<Self>) {
        let Some(entry) = self.diaries.iter_mut().find(|entry| entry.id == diary_id) else { return; };
        if from >= entry.photos.len() || to >= entry.photos.len() || from == to { return; }
        let current_photo = entry.photos.get(self.diary_photo_index).cloned();
        let moved = entry.photos.remove(from);
        entry.photos.insert(to.min(entry.photos.len()), moved);
        if let Some(current_photo) = current_photo {
            self.diary_photo_index = entry.photos.iter().position(|photo| photo == &current_photo).unwrap_or(0);
        }
        self.notice = Some("日记中的媒体顺序已更新。".into());
        self.save_diary_data(cx);
    }

    fn save_diary_draft(&mut self, cx: &mut Context<Self>) {
        if let Some(field) = &self.diary_title_edit { self.diary_title_draft = field.read(cx).content.to_string(); }
        if let Some(field) = &self.diary_body_edit { self.diary_body_draft = field.read(cx).content.to_string(); }
        let Some(id) = self.selected_diary else { return };
        if let Some(entry) = self.diaries.iter_mut().find(|entry| entry.id == id) {
            entry.category = self.diary_category_draft.clone();
            entry.title = if self.diary_title_draft.trim().is_empty() { "无标题日记".into() } else { self.diary_title_draft.trim().into() };
            entry.body = self.diary_body_draft.clone();
        }
        if self.diary_filter != "全部" && self.diary_filter != self.diary_category_draft { self.diary_filter = "全部".into(); }
        self.diary_editing = false;
        self.notice = Some("日记已保存。".into());
        self.save_diary_data(cx);
    }

    fn delete_selected_diary(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.selected_diary.take() else { return };
        let Some(index) = self.diaries.iter().position(|entry| entry.id == id) else { return };
        let entry = self.diaries.remove(index);
        let previous_trash = self.diary_trash.clone();
        self.diary_trash.insert(0, entry.clone());
        self.diary_editing = false;
        if let Err(error) = save_diary_trash(&self.diary_trash) {
            self.diary_trash = previous_trash;
            self.diaries.insert(index, entry);
            self.selected_diary = Some(id);
            self.notice = Some(format!("移入回收站失败：{error}"));
        } else if let Err(error) = save_diaries(&self.diaries) {
            self.diary_trash = previous_trash;
            self.diaries.insert(index, entry);
            self.selected_diary = Some(id);
            let _ = save_diary_trash(&self.diary_trash);
            self.notice = Some(format!("保存日记失败：{error}"));
        } else {
            self.notice = Some("日记已移入日记回收站，可恢复或彻底删除。".into());
        }
        cx.notify();
    }

    fn restore_trashed_diary(&mut self, id: u64, cx: &mut Context<Self>) {
        let Some(index) = self.diary_trash.iter().position(|entry| entry.id == id) else {
            self.notice = Some("回收站中没有找到这篇日记。".into());
            cx.notify();
            return;
        };
        let entry = self.diary_trash.remove(index);
        self.diaries.insert(0, entry.clone());
        if let Err(error) = save_diaries(&self.diaries) {
            self.diaries.remove(0);
            self.diary_trash.insert(index, entry);
            self.notice = Some(format!("恢复日记失败：{error}"));
        } else if let Err(error) = save_diary_trash(&self.diary_trash) {
            self.diaries.remove(0);
            self.diary_trash.insert(index, entry);
            let _ = save_diaries(&self.diaries);
            let _ = save_diary_trash(&self.diary_trash);
            self.notice = Some(format!("更新回收站失败，日记已保留在回收站：{error}"));
        } else {
            self.selected_diary = Some(id);
            self.diary_editing = false;
            self.diary_photo_index = 0;
            self.notice = Some("日记已恢复，并已在日记栏中打开。".into());
            self.set_section("日记", cx);
        }
        cx.notify();
    }

    fn permanently_delete_trashed_diary(&mut self, id: u64, cx: &mut Context<Self>) {
        if let Some(index) = self.diary_trash.iter().position(|entry| entry.id == id) {
            let entry = self.diary_trash.remove(index);
            match save_diary_trash(&self.diary_trash) {
                Ok(()) => self.notice = Some("日记已从回收站彻底删除。".into()),
                Err(error) => {
                    self.diary_trash.insert(index, entry);
                    self.notice = Some(format!("彻底删除失败：{error}"));
                }
            }
        }
        cx.notify();
    }

    fn drag_paths_for(&self, path: &Path) -> Vec<PathBuf> {
        if !self.selected_paths.contains(path) { return vec![path.to_path_buf()]; }
        self.visible_media().into_iter()
            .filter_map(|index| self.photos.get(index))
            .filter(|candidate| self.selected_paths.contains(*candidate))
            .cloned()
            .collect()
    }

    fn select_media(&mut self, index: usize, shift: bool) {
        self.selected_media = index;
        let visible = if self.selection_display_order.is_empty() { self.visible_media() } else { self.selection_display_order.clone() };
        if shift {
            let anchor = self.selection_anchor.as_ref()
                .and_then(|path| self.photos.iter().position(|photo| photo == path))
                .and_then(|anchor| visible.iter().position(|visible_index| *visible_index == anchor))
                .or_else(|| visible.iter().position(|visible_index| *visible_index == index));
            let Some(anchor) = anchor else { return; };
            let Some(clicked) = visible.iter().position(|visible_index| *visible_index == index) else {
                self.selected_paths.clear();
                if let Some(path) = self.photos.get(index) { self.selected_paths.insert(path.clone()); }
                self.selection_anchor = self.photos.get(index).cloned();
                return;
            };
            let start = anchor.min(clicked);
            let end = anchor.max(clicked);
            self.selected_paths = visible[start..=end].iter().filter_map(|i| self.photos.get(*i).cloned()).collect();
        } else {
            let clicked_is_selected = self.photos.get(index).is_some_and(|path| self.selected_paths.contains(path));
            if !clicked_is_selected {
                self.selected_paths.clear();
                if let Some(path) = self.photos.get(index) { self.selected_paths.insert(path.clone()); }
                self.selection_anchor = self.photos.get(index).cloned();
            }
        }
    }

    fn photo_context_menu(&mut self, path: PathBuf, _hover_group: &str, cx: &mut Context<Self>) -> gpui::AnyElement {
        if self.photo_context_menu.as_ref() != Some(&path) {
            return div().into_any_element();
        }
        let copy_path = path.clone();
        let reveal_path = path.clone();
        let delete_path = path.clone();
        let select_path = path.clone();
        let is_selected = self.selected_paths.contains(&path);
        let menu = div()
            .absolute()
            .top(px(6.))
            .left(px(6.))
            .w(px(172.))
            .flex()
            .flex_col()
            .gap_0()
            .p_1()
            .rounded_lg()
            .border_1()
            .border_color(rgba(0xffffff55))
            .bg(rgba(0x393b42d9))
            .child(button("拷贝照片", false).w_full().px_2().py_2().text_sm().text_color(rgb(0xf6f5f2)).bg(rgba(0x20212400)).hover(|style| style.bg(rgba(0xffffff30))).on_click(cx.listener(move |this, _, _, cx| {
                this.copy_photo(&copy_path);
                this.photo_context_menu = None;
                cx.notify();
            })))
            .child(button(if is_selected { "移出多选" } else { "加入多选" }, false).w_full().px_2().py_2().text_sm().text_color(rgb(0xf6f5f2)).bg(rgba(0x20212400)).hover(|style| style.bg(rgba(0xffffff30))).on_click(cx.listener(move |this, _, _, cx| {
                if !this.selected_paths.remove(&select_path) { this.selected_paths.insert(select_path.clone()); }
                this.photo_context_menu = None;
                cx.notify();
            })))
            .child(button("在访达中显示", false).w_full().px_2().py_2().text_sm().text_color(rgb(0xf6f5f2)).bg(rgba(0x20212400)).hover(|style| style.bg(rgba(0xffffff30))).on_click(cx.listener(move |this, _, _, cx| {
                this.reveal_photo(&reveal_path);
                this.photo_context_menu = None;
                cx.notify();
            })))
            .child(button("移至删除区域", false).w_full().px_2().py_2().text_sm().text_color(rgb(0xf6f5f2)).bg(rgba(0x20212400)).hover(|style| style.bg(rgba(0xffffff30))).on_click(cx.listener(move |this, _, window, cx| {
                let mouse = window.mouse_position();
                let position = this.last_selection_position.unwrap_or((mouse.x.to_f64() as f32, mouse.y.to_f64() as f32));
                this.move_photo_to_trash(&delete_path, position, cx);
                this.photo_context_menu = None;
                this.photo_context_menu_hovered = false;
                cx.notify();
            })))
            .id("photo-context-menu")
            .on_hover(cx.listener(|this, hovered: &bool, _, cx| {
            if *hovered {
                this.photo_context_menu_hovered = true;
            } else if this.photo_context_menu_hovered {
                this.photo_context_menu = None;
                this.photo_context_menu_hovered = false;
                cx.notify();
            }
        }));
        menu.into_any_element()
    }

    fn copy_photo(&mut self, path: &Path) {
        let result = Command::new("/usr/bin/osascript")
            .arg("-e")
            .arg("on run argv\nset the clipboard to (POSIX file (item 1 of argv))\nend run")
            .arg(path)
            .output();
        self.notice = match result {
            Ok(result) if result.status.success() => Some("照片已复制，可粘贴到其他应用。".into()),
            Ok(result) => Some(format!("复制照片失败：{}", String::from_utf8_lossy(&result.stderr).trim())),
            Err(error) => Some(format!("复制照片失败：{error}")),
        };
    }

    fn copy_selected_photos(&mut self) {
        let paths: Vec<_> = self.selected_paths.iter().filter(|path| path.is_file()).cloned().collect();
        if paths.is_empty() { self.notice = Some("请先在照片菜单中加入要拷贝的照片。".into()); return; }
        let script = "on run argv\nset fileList to {}\nrepeat with p in argv\nset end of fileList to POSIX file p\nend repeat\nset the clipboard to fileList\nend run";
        match Command::new("/usr/bin/osascript").arg("-e").arg(script).args(&paths).output() {
            Ok(result) if result.status.success() => self.notice = Some(format!("已拷贝 {} 个项目，可粘贴到其他应用。", paths.len())),
            Ok(result) => self.notice = Some(format!("拷贝失败：{}", String::from_utf8_lossy(&result.stderr).trim())),
            Err(error) => self.notice = Some(format!("拷贝失败：{error}")),
        }
    }

    fn delete_selected_photos(&mut self, cx: &mut Context<Self>) {
        let Some(root) = self.source_directory.clone() else { self.notice = Some("请先选择照片目录。".into()); cx.notify(); return; };
        let paths: Vec<_> = self.selected_paths.iter().cloned().collect();
        if paths.is_empty() { self.notice = Some("请先选择照片。".into()); cx.notify(); return; }
        let mut moved = 0;
        let mut errors = Vec::new();
        let mut flight_thumbnail = None;
        for path in &paths {
            let thumbnail = self.prepare_delete_flight_thumbnail(path);
            match move_to_deletion_area(&root, path) {
                Ok(_) => {
                    self.remove_media_from_gallery(path);
                    moved += 1;
                    if flight_thumbnail.is_none() { flight_thumbnail = thumbnail; }
                    else if let Some(thumbnail) = thumbnail { let _ = fs::remove_file(thumbnail); }
                }
                Err(error) => {
                    if let Some(thumbnail) = thumbnail { let _ = fs::remove_file(thumbnail); }
                    errors.push(format!("{}：{}", filename(path), error));
                }
            }
        }
        if let Some(thumbnail) = flight_thumbnail {
            let (x, y) = self.last_selection_position.unwrap_or((360., 280.));
            self.trigger_photo_delete_flight(thumbnail, (x, y), cx);
        }
        self.selected_paths.clear();
        self.notice = Some(if errors.is_empty() { format!("已将 {moved} 个项目移至删除区域，可恢复或永久删除。") } else { format!("已移动 {moved} 项；失败 {} 项：{}", errors.len(), errors.join("；")) });
        cx.notify();
    }

    fn reveal_photo(&mut self, path: &Path) {
        match Command::new("/usr/bin/open").arg("-R").arg(path).status() {
            Ok(status) if status.success() => self.notice = None,
            Ok(_) => self.notice = Some("无法在访达中定位这张照片。".into()),
            Err(error) => self.notice = Some(format!("无法打开访达：{error}")),
        }
    }

    fn move_photo_to_trash(&mut self, path: &Path, position: (f32, f32), cx: &mut Context<Self>) {
        let Some(root) = self.source_directory.clone() else {
            self.notice = Some("请先选择照片目录。".into());
            return;
        };
        let thumbnail = self.prepare_delete_flight_thumbnail(path);
        match move_to_deletion_area(&root, path) {
            Ok(_) => {
                self.remove_media_from_gallery(path);
                if let Some(thumbnail) = thumbnail { self.trigger_photo_delete_flight(thumbnail, position, cx); }
                self.notice = Some("媒体已移至删除区域，可在其中恢复或永久删除。".into());
            }
            Err(error) => {
                if let Some(thumbnail) = thumbnail { let _ = fs::remove_file(thumbnail); }
                self.notice = Some(format!("移至删除区域失败：{error}"));
            }
        }
    }

    fn prepare_delete_flight_thumbnail(&mut self, path: &Path) -> Option<PathBuf> {
        let preview = self.video_thumbnails.get(path)
            .or_else(|| self.photo_thumbnails.get(path))
            .or_else(|| self.heic_previews.get(path))
            .filter(|thumbnail| thumbnail.is_file())
            .cloned()
            .or_else(|| {
                let display = self.heic_previews.get(path).cloned().unwrap_or_else(|| path.to_path_buf());
                generate_photo_thumbnail(path, &display)
            })?;
        self.photo_delete_flight_id = self.photo_delete_flight_id.wrapping_add(1);
        let next_id = self.photo_delete_flight_id;
        let snapshot = env::temp_dir().join(format!("guangyu-delete-flight-{next_id}.jpg"));
        fs::copy(preview, &snapshot).ok()?;
        Some(snapshot)
    }

    fn trigger_photo_delete_flight(&mut self, thumbnail: PathBuf, position: (f32, f32), cx: &mut Context<Self>) {
        self.trigger_photo_flight_to(thumbnail, position, (f32::NAN, f32::NAN), cx);
    }

    fn trigger_photo_flight_to(&mut self, thumbnail: PathBuf, position: (f32, f32), destination: (f32, f32), cx: &mut Context<Self>) {
        self.photo_delete_flight_id = self.photo_delete_flight_id.wrapping_add(1);
        let flight_id = self.photo_delete_flight_id;
        self.photo_delete_flight = Some((thumbnail.clone(), position.0, position.1, destination.0, destination.1, flight_id));
        cx.spawn(async move |this, cx| {
            cx.background_executor().timer(Duration::from_millis(900)).await;
            let _ = this.update(cx, |app, cx| {
                if app.photo_delete_flight.as_ref().is_some_and(|(_, _, _, _, _, id)| *id == flight_id) {
                    app.photo_delete_flight = None;
                    let _ = fs::remove_file(&thumbnail);
                    cx.notify();
                }
            });
        }).detach();
    }

    fn remove_media_from_gallery(&mut self, path: &Path) {
        self.photos.retain(|photo| photo != path);
        self.capture_dates.remove(path);
        self.capture_locations.remove(path);
        self.video_thumbnails.remove(path);
        self.photo_thumbnails.remove(path);
        self.photo_rotations.remove(path);
        self.rotated_photo_paths.remove(path);
        for items in self.category_items.values_mut() { items.remove(path); }
        self.duplicate_selected.remove(path);
        self.selected_paths.remove(path);
        for group in &mut self.duplicate_groups { group.retain(|item| item != path); }
        self.duplicate_groups.retain(|group| group.len() > 1);
        self.selected_media = self.selected_media.min(self.photos.len().saturating_sub(1));
        self.save_category_index();
    }

    fn move_dragged_to_quarantine(&mut self, path: &Path, source_category: Option<&str>, position: (f32, f32), cx: &mut Context<Self>) {
        let Some(root) = self.source_directory.clone() else { self.notice = Some("请先选择照片目录。".into()); cx.notify(); return; };
        match quarantine_files(&root, &[path.to_path_buf()]) {
            Ok(_) => {
                self.remove_media_from_gallery(path);
                self.notice = Some(format!("已将“{}”移入隔离区，可随时恢复。", filename(path)));
                if source_category.is_some() { self.trigger_category_removal_effect(position, cx); }
            }
            Err(error) => self.notice = Some(format!("移入隔离区失败：{error}")),
        }
        cx.notify();
    }

    fn move_dragged_to_deletion_area(&mut self, path: &Path, source_category: Option<&str>, position: (f32, f32), cx: &mut Context<Self>) {
        let Some(root) = self.source_directory.as_deref() else { self.notice = Some("请先选择照片目录。".into()); cx.notify(); return; };
        match move_to_deletion_area(root, path) {
            Ok(_) => {
                self.remove_media_from_gallery(path);
                self.notice = Some(format!("已将“{}”移至删除区域，可恢复或永久删除。", filename(path)));
                if source_category.is_some() { self.trigger_category_removal_effect(position, cx); }
            }
            Err(error) => self.notice = Some(format!("移至删除区域失败：{error}")),
        }
        cx.notify();
    }

    fn permanently_delete_from_area(&mut self, path: &Path, cx: &mut Context<Self>) {
        if self.pending_permanent_delete.as_deref() != Some(path) {
            self.pending_permanent_delete = Some(path.to_path_buf());
            self.notice = Some("再次点击“确认永久删除”以不可恢复地删除此文件。".into());
            cx.notify();
            return;
        }
        match fs::remove_file(path) {
            Ok(()) => {
                remove_photo_thumbnail_cache(path);
                self.pending_permanent_delete = None;
                self.notice = Some("照片已永久删除。".into());
            }
            Err(error) => self.notice = Some(format!("永久删除失败：{error}")),
        }
        cx.notify();
    }

    fn photo_thumbnail(&mut self, source: &Path, display_source: &Path, cx: &mut Context<Self>) -> Option<PathBuf> {
        if let Some(thumbnail) = self.photo_thumbnails.get(source).filter(|path| path.is_file()) {
            return Some(thumbnail.clone());
        }
        if self.photo_rotation_requests.contains(source) {
            return None;
        }
        let requested_rotation = self.photo_rotations.get(source).copied().unwrap_or(0);
        let cache_path = photo_thumbnail_cache_path_for_rotation(source, requested_rotation);
        if let Some(thumbnail) = cache_path.as_ref().filter(|path| path.is_file()) {
            self.photo_thumbnails.insert(source.to_path_buf(), thumbnail.clone());
            return Some(thumbnail.clone());
        }
        if !self.photo_thumbnail_failures.contains(source) && self.photo_thumbnail_requests.insert(source.to_path_buf()) {
            let source_path = source.to_path_buf();
            let input_path = display_source.to_path_buf();
            let generated_cache_path = cache_path;
            let task_source_path = source_path.clone();
            cx.spawn(async move |this, cx| {
                let generated = cx.background_executor().spawn(async move {
                    generate_photo_thumbnail_for_rotation(&task_source_path, &input_path, requested_rotation)
                }).await;
                let _ = this.update(cx, |view, cx| {
                    view.photo_thumbnail_requests.remove(&source_path);
                    let current_rotation = view.photo_rotations.get(&source_path).copied().unwrap_or(0);
                    if current_rotation != requested_rotation {
                        if let Some(path) = generated_cache_path { let _ = fs::remove_file(path); }
                    } else if let Some(thumbnail) = generated {
                        view.photo_thumbnails.insert(source_path, thumbnail);
                    } else {
                        view.photo_thumbnail_failures.insert(source_path);
                    }
                    cx.notify();
                });
            }).detach();
        }
        None
    }

    fn restore_from_deletion_area(&mut self, path: &Path, cx: &mut Context<Self>) {
        let Some(root) = self.source_directory.clone() else { return };
        match restore_deletion_area_file(&root, path) {
            Ok(restored) => {
                self.photos.push(restored);
                self.photos.sort();
                self.photos.dedup();
                self.notice = Some("照片已恢复到原位置。".into());
            }
            Err(error) => self.notice = Some(format!("恢复照片失败：{error}")),
        }
        self.pending_permanent_delete = None;
        cx.notify();
    }

    fn open_photo_context_menu(&mut self, path: PathBuf, position: gpui::Point<gpui::Pixels>, cx: &mut Context<Self>) {
        self.selected_media = self.photos.iter().position(|photo| photo == &path).unwrap_or(self.selected_media);
        self.last_selection_position = Some((position.x.to_f64() as f32, position.y.to_f64() as f32));
        self.photo_context_menu = Some(path);
        self.photo_context_menu_hovered = false;
        cx.notify();
    }

    fn photo_display_path(&mut self, source: &Path, cx: &mut Context<Self>) -> PathBuf {
        if is_heic(source) && !self.photo_rotations.contains_key(source) {
            if let Some(preview) = self.heic_previews.get(source).filter(|path| path.is_file()) {
                return preview.clone();
            }
            if !self.heic_preview_failures.contains(source)
                && self.heic_preview_requests.insert(source.to_path_buf())
            {
                let source_path = source.to_path_buf();
                let task_path = source_path.clone();
                cx.spawn(async move |this, cx| {
                    let preview = cx.background_executor().spawn(async move { generate_heic_preview(&task_path) }).await;
                    let _ = this.update(cx, |view, cx| {
                        view.heic_preview_requests.remove(&source_path);
                        if let Some(preview) = preview {
                            view.heic_previews.insert(source_path, preview);
                        } else {
                            view.heic_preview_failures.insert(source_path);
                        }
                        cx.notify();
                    });
                }).detach();
            }
            return source.to_path_buf();
        }
        let Some(degrees) = self.photo_rotations.get(source).copied() else {
            return source.to_path_buf();
        };
        if let Some(path) = self.rotated_photo_paths.get(source) {
            if rotated_photo_cache_path(source, degrees).as_ref() == Some(path) && path.is_file() {
                return path.clone();
            }
            self.rotated_photo_paths.remove(source);
        }
        if self.photo_rotation_failures.contains(source) {
            return source.to_path_buf();
        }
        if let Some(cache_path) = rotated_photo_cache_path(source, degrees)
            && cache_path.is_file()
        {
            self.rotated_photo_paths
                .insert(source.to_path_buf(), cache_path.clone());
            return cache_path;
        }
        if self.photo_rotation_requests.insert(source.to_path_buf()) {
            let source_path = source.to_path_buf();
            let task_path = source_path.clone();
            cx.spawn(async move |this, cx| {
                let task_source_for_thumbnail = task_path.clone();
                let (rotated, thumbnail) = cx.background_executor().spawn(async move {
                    let rotated = generate_rotated_photo(&task_path, degrees);
                    let thumbnail = rotated.as_ref().and_then(|display| {
                        generate_photo_thumbnail_for_rotation(&task_source_for_thumbnail, display, degrees)
                    });
                    (rotated, thumbnail)
                }).await;
                let _ = this.update(cx, |view, cx| {
                    view.photo_rotation_requests.remove(&source_path);
                    if view.photo_rotations.get(&source_path) == Some(&degrees) {
                        if let Some(rotated) = rotated {
                            view.rotated_photo_paths
                                .insert(source_path.clone(), rotated);
                            if let Some(thumbnail) = thumbnail {
                                view.photo_thumbnails.insert(source_path.clone(), thumbnail);
                                view.photo_thumbnail_failures.remove(&source_path);
                            }
                        } else {
                            view.photo_rotation_failures.insert(source_path.clone());
                            view.notice = Some("无法生成旋转后的照片预览。".to_string());
                        }
                        cx.notify();
                    } else {
                        remove_photo_thumbnail_cache(&source_path);
                        let _ = view.photo_display_path(&source_path, cx);
                    }
                });
            })
            .detach();
        }
        source.to_path_buf()
    }

    fn request_image_dimensions(&mut self, path: &Path, cx: &mut Context<Self>) {
        if self.image_dimensions.contains_key(path) || !self.image_dimensions_requests.insert(path.to_path_buf()) { return; }
        let path = path.to_path_buf();
        let task_path = path.clone();
        cx.spawn(async move |this, cx| {
            let dimensions = cx.background_executor().spawn(async move {
                let label = image_dimensions(&task_path);
                let size = thumbnail_dimensions(&task_path);
                (label, size)
            }).await;
            let _ = this.update(cx, |view, cx| {
                view.image_dimensions_requests.remove(&path);
                view.image_dimensions.insert(path.clone(), dimensions.0);
                view.image_sizes.insert(path, dimensions.1);
                cx.notify();
            });
        }).detach();
    }

    fn rotate_photo(&mut self, source: PathBuf, cx: &mut Context<Self>) {
        if is_supported_video(&source) {
            return;
        }
        let degrees = (self.photo_rotations.get(&source).copied().unwrap_or(0) + 90) % 360;
        let current_rotation = self.photo_rotations.get(&source).copied().unwrap_or(0);
        let current_thumbnail = self.photo_thumbnails.get(&source)
            .filter(|path| path.is_file())
            .cloned()
            .or_else(|| photo_thumbnail_cache_path_for_rotation(&source, current_rotation).filter(|path| path.is_file()))
            .or_else(|| {
                let current_display = self.rotated_photo_paths.get(&source).cloned()
                    .or_else(|| (current_rotation != 0).then(|| rotated_photo_cache_path(&source, current_rotation)).flatten().filter(|path| path.is_file()))
                    .unwrap_or_else(|| source.clone());
                generate_photo_thumbnail_for_rotation(&source, &current_display, current_rotation)
            });
        if let Some(current_thumbnail) = current_thumbnail {
            if let Some(rotated_thumbnail) = generate_rotated_thumbnail_preview(&source, &current_thumbnail) {
                self.photo_thumbnails.insert(source.clone(), rotated_thumbnail);
            }
        }
        self.photo_thumbnail_failures.remove(&source);
        if degrees == 0 {
            self.photo_rotations.remove(&source);
            self.rotated_photo_paths.remove(&source);
            self.photo_rotation_failures.remove(&source);
        } else {
            self.photo_rotations.insert(source.clone(), degrees);
            self.rotated_photo_paths.remove(&source);
            self.photo_rotation_failures.remove(&source);
        }
        let settings = self.photo_rotations.clone();
        let persist_error = persist_photo_rotations(&settings).err();
        self.notice = persist_error.map(|error| format!("照片已旋转，但设置保存失败：{error}"));
        cx.notify();
        if degrees != 0 {
            let _ = self.photo_display_path(&source, cx);
        }
    }

    fn toggle_video_playback(&mut self, path: PathBuf, cx: &mut Context<Self>) {
        if let Some(playback) = &mut self.video_playback
            && playback.path == path
        {
            if playback.playing {
                unsafe { playback.player.pause() };
                playback.playing = false;
            } else {
                let current = unsafe { playback.player.currentTime().seconds() };
                let duration = unsafe { playback.item.duration().seconds() };
                if duration.is_finite() && current >= duration {
                    unsafe { playback.player.seekToTime(CMTime::with_seconds(0.0, 600)) };
                }
                unsafe { playback.player.play() };
                playback.playing = true;
            }
            cx.notify();
            return;
        }

        let Some(main_thread) = MainThreadMarker::new() else {
            self.notice = Some("视频播放器需要在 macOS 主线程中启动。".to_string());
            cx.notify();
            return;
        };
        let Some(path_text) = path.to_str() else {
            self.notice = Some("视频路径包含无法识别的字符。".to_string());
            cx.notify();
            return;
        };

        let url = NSURL::fileURLWithPath(&NSString::from_str(path_text));
        let item = unsafe { AVPlayerItem::playerItemWithURL(&url, main_thread) };
        let key = NSString::from_str("PixelFormatType");
        let pixel_format = NSNumber::numberWithUnsignedInt(0x34323066);
        let key_protocol = objc2::runtime::ProtocolObject::from_ref(&*key);
        let attributes: Retained<NSDictionary<NSString, AnyObject>> =
            unsafe { NSDictionary::dictionaryWithObject_forKey(&*pixel_format, &key_protocol) };
        let output = unsafe {
            AVPlayerItemVideoOutput::initWithPixelBufferAttributes(
                AVPlayerItemVideoOutput::alloc(),
                Some(&attributes),
            )
        };
        unsafe { item.addOutput(&output) };
        let player = unsafe { AVPlayer::playerWithPlayerItem(Some(&item), main_thread) };
        unsafe { player.play() };
        self.video_playback = Some(VideoPlayback {
            path,
            player,
            item,
            output,
            frame: None,
            playing: true,
        });
        self.notice = None;
        cx.notify();
    }

    fn seek_video(&mut self, path: &Path, offset_seconds: f64, cx: &mut Context<Self>) {
        let Some(playback) = self
            .video_playback
            .as_ref()
            .filter(|playback| playback.path == path)
        else {
            return;
        };
        let current = unsafe { playback.player.currentTime().seconds() };
        let duration = unsafe { playback.item.duration().seconds() };
        if !current.is_finite() {
            return;
        }
        let target = if duration.is_finite() && duration > 0.0 {
            (current + offset_seconds).clamp(0.0, duration)
        } else {
            (current + offset_seconds).max(0.0)
        };
        unsafe {
            playback
                .player
                .seekToTime(CMTime::with_seconds(target, 600))
        };
        cx.notify();
    }

    fn seek_video_to_ratio(&mut self, path: &Path, ratio: f64, cx: &mut Context<Self>) {
        let Some(playback) = self
            .video_playback
            .as_ref()
            .filter(|playback| playback.path == path)
        else {
            return;
        };
        let duration = unsafe { playback.item.duration().seconds() };
        if duration.is_finite() && duration > 0.0 {
            let target = duration * ratio.clamp(0.0, 1.0);
            unsafe {
                playback
                    .player
                    .seekToTime(CMTime::with_seconds(target, 600))
            };
            self.video_seeking = true;
            cx.notify();
        }
    }

    fn update_video_frame(&mut self) {
        let Some(playback) = &mut self.video_playback else {
            return;
        };
        let time = unsafe { playback.player.currentTime() };
        let current_seconds = unsafe { time.seconds() };
        let duration_seconds = unsafe { playback.item.duration().seconds() };
        if playback.playing && duration_seconds.is_finite() && current_seconds >= duration_seconds {
            unsafe { playback.player.pause() };
            playback.playing = false;
            return;
        }
        if !unsafe { playback.output.hasNewPixelBufferForItemTime(time) } {
            return;
        }
        let Some(frame) = (unsafe {
            playback
                .output
                .copyPixelBufferForItemTime_itemTimeForDisplay(time, std::ptr::null_mut())
        }) else {
            return;
        };
        let frame = unsafe {
            <core_video::pixel_buffer::CVPixelBuffer as core_foundation::base::TCFType>::wrap_under_get_rule(
                Retained::as_ptr(&frame) as core_video::pixel_buffer::CVPixelBufferRef,
            )
        };
        playback.frame = Some(frame);
    }

    fn stop_video_if_not_selected(&mut self, selected: &Path) {
        if self
            .video_playback
            .as_ref()
            .is_some_and(|playback| playback.path != selected)
        {
            if let Some(playback) = self.video_playback.take() {
                unsafe { playback.player.pause() };
            }
        }
    }

    fn video_thumbnail(&mut self, path: &Path, cx: &mut Context<Self>) -> Option<PathBuf> {
        if !is_supported_video(path) {
            return None;
        }
        if let Some(thumbnail) = self.video_thumbnails.get(path) {
            return Some(thumbnail.clone());
        }
        if let Some(thumbnail) = video_thumbnail_cache_path(path).filter(|path| path.is_file()) {
            self.video_thumbnails
                .insert(path.to_path_buf(), thumbnail.clone());
            return Some(thumbnail);
        }
        if self.video_thumbnail_failures.contains(path) {
            return None;
        }
        if self.video_thumbnail_requests.insert(path.to_path_buf()) {
            let source = path.to_path_buf();
            let source_for_task = source.clone();
            cx.spawn(async move |this, cx| {
                let thumbnail = cx
                    .background_executor()
                    .spawn(async move { generate_video_thumbnail(&source_for_task) })
                    .await;
                let _ = this.update(cx, |view, cx| {
                    view.video_thumbnail_requests.remove(&source);
                    if let Some(thumbnail) = thumbnail {
                        view.video_thumbnails.insert(source, thumbnail);
                    } else {
                        view.video_thumbnail_failures.insert(source);
                    }
                    cx.notify();
                });
            })
            .detach();
        }
        None
    }

    fn open_media(&mut self, path: PathBuf, cx: &mut Context<Self>) {
        if is_supported_video(&path) {
            if let Err(error) = Command::new("open").arg(&path).spawn() {
                self.notice = Some(format!("无法打开视频：{error}"));
                cx.notify();
            }
            return;
        }
        let title = filename(&path);
        let display_path = self.photo_display_path(&path, cx);
        let bounds = Bounds::centered(None, size(px(980.), px(720.)), cx);
        let _ = cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                is_resizable: true,
                window_min_size: Some(size(px(480.), px(360.))),
                ..Default::default()
            },
            move |window, cx| {
                window.set_window_title(&title);
                cx.new(|_| PhotoViewer { path: display_path })
            },
        );
    }

    fn set_section(&mut self, name: &str, cx: &mut Context<Self>) {
        if name == "日记" {
            self.diary_column_open = true;
            cx.notify();
            return;
        }
        self.selected_section = name.to_string();
        cx.notify();
    }

    fn close_diary_column(&mut self, cx: &mut Context<Self>) {
        self.diary_column_open = false;
        self.diary_zoom_photo = None;
        cx.notify();
    }

    fn toggle_diary_column(&mut self, cx: &mut Context<Self>) {
        self.diary_column_open = !self.diary_column_open;
        if !self.diary_column_open { self.diary_zoom_photo = None; }
        cx.notify();
    }

    fn set_mode(&mut self, mode: ViewMode, cx: &mut Context<Self>) {
        self.view_mode = mode;
        cx.notify();
    }

    fn add_category(&mut self, cx: &mut Context<Self>) {
        if let Some(name) = prompt_category_name("", false) { self.submit_category_name(name, None, cx); }
    }

    fn save_category_index(&self) {
        let Some(path) = category_index_path() else { return };
        if let Some(parent) = path.parent() { let _ = fs::create_dir_all(parent); }
        let mut lines = vec!["GUANGYU-CATEGORIES-1".to_string()];
        for name in &self.categories {
            lines.push(format!("C\t{}", hex_encode(name.as_bytes())));
            if let Some(items) = self.category_items.get(name) {
                for item in items {
                    lines.push(format!("P\t{}\t{}", hex_encode(name.as_bytes()), hex_encode(item.to_string_lossy().as_bytes())));
                }
            }
        }
        let _ = fs::write(path, lines.join("\n"));
    }

    fn submit_category_name(&mut self, name: String, rename_target: Option<String>, cx: &mut Context<Self>) {
        let name = name.trim().to_string();
        if name.is_empty() { self.notice = Some("请输入分类名称。".into()); cx.notify(); return; }
        if self.categories.iter().any(|existing| existing == &name && rename_target.as_ref() != Some(existing)) {
            self.notice = Some("已有同名分类，请换一个名称。".into()); cx.notify(); return;
        }
        if let Some(old) = rename_target {
            if old != name {
                if let Some(index) = self.categories.iter().position(|item| item == &old) { self.categories[index] = name.clone(); }
                if let Some(items) = self.category_items.remove(&old) { self.category_items.insert(name.clone(), items); }
                if self.selected_section == old { self.selected_section = name.clone(); }
            }
        } else {
            self.categories.push(name.clone());
            self.category_items.entry(name.clone()).or_default();
            self.selected_section = name.clone();
        }
        self.notice = None;
        self.save_category_index();
        cx.notify();
    }

    fn rename_category(&mut self, name: &str, cx: &mut Context<Self>) {
        if let Some(new_name) = prompt_category_name(name, true) { self.submit_category_name(new_name, Some(name.to_string()), cx); }
    }

    fn delete_category(&mut self, name: &str, cx: &mut Context<Self>) {
        self.categories.retain(|item| item != name);
        self.category_items.remove(name);
        if self.selected_section == name { self.selected_section = "管理分类".into(); }
        self.save_category_index();
        self.notice = Some(format!("已删除分类“{name}”，照片文件保持原位。"));
        cx.notify();
    }

    fn add_selected_to_category(&mut self, name: &str, cx: &mut Context<Self>) {
        let Some(path) = self.visible_media().get(self.selected_media).and_then(|index| self.photos.get(*index)).cloned() else {
            self.notice = Some("请先选中一张照片。".into()); cx.notify(); return;
        };
        self.category_items.entry(name.to_string()).or_default().insert(path);
        self.save_category_index();
        self.notice = Some(format!("已加入“{name}”。"));
        cx.notify();
    }

    fn add_path_to_category(&mut self, name: &str, path: &Path, cx: &mut Context<Self>) {
        if !self.photos.iter().any(|photo| photo == path) { return; }
        self.category_items.entry(name.to_string()).or_default().insert(path.to_path_buf());
        self.save_category_index();
        self.notice = Some(format!("已将“{}”加入“{name}”。", filename(path)));
        cx.notify();
    }

    fn add_paths_to_category(&mut self, name: &str, paths: &[PathBuf], cx: &mut Context<Self>) {
        let items = self.category_items.entry(name.to_string()).or_default();
        let mut added = 0;
        for path in paths {
            if self.photos.iter().any(|photo| photo == path) && items.insert(path.clone()) { added += 1; }
        }
        self.save_category_index();
        self.notice = Some(format!("已将 {added} 张照片加入“{name}”。"));
        cx.notify();
    }

    fn trigger_category_removal_effect(&mut self, position: (f32, f32), cx: &mut Context<Self>) {
        self.category_removal_effect_id = self.category_removal_effect_id.wrapping_add(1);
        let effect_id = self.category_removal_effect_id;
        self.category_removal_effect = Some((position.0, position.1, effect_id));
        cx.spawn(async move |this, cx| {
            cx.background_executor().timer(Duration::from_millis(700)).await;
            let _ = this.update(cx, |app, cx| {
                if app.category_removal_effect.as_ref().is_some_and(|(_, _, id)| *id == effect_id) {
                    app.category_removal_effect = None;
                    cx.notify();
                }
            });
        }).detach();
    }

    fn remove_paths_from_category(&mut self, category: &str, paths: &[PathBuf], position: (f32, f32), cx: &mut Context<Self>) {
        let mut removed = 0;
        if let Some(items) = self.category_items.get_mut(category) {
            for path in paths { if items.remove(path) { removed += 1; } }
        }
        if removed > 0 {
            self.save_category_index();
            self.notice = Some(format!("已将 {removed} 张照片移出分类“{category}”。"));
            self.trigger_category_removal_effect(position, cx);
            for path in paths { self.selected_paths.remove(path); }
            cx.notify();
        } else {
            cx.notify();
        }
    }

    fn set_sort_mode(&mut self, mode: SortMode, cx: &mut Context<Self>) {
        self.sort_mode = mode;
        self.sort_menu_open = false;
        cx.notify();
    }

    fn refresh_iphone(&mut self, cx: &mut Context<Self>) {
        self.connected_iphone = connected_iphone_name();
        self.notice = Some(match &self.connected_iphone {
            Some(name) => format!("已检测到 {name}。直接导入功能正在接入。"),
            None => "未检测到通过 USB 连接的 iPhone。".to_string(),
        });
        cx.notify();
    }

    fn open_image_capture(&mut self, cx: &mut Context<Self>) {
        let result = Command::new("open").args(["-a", "Image Capture"]).status();
        self.notice = Some(match result {
            Ok(status) if status.success() => "已打开 macOS「图像捕捉」。将照片或视频导入当前浏览目录后，光屿会自动刷新图库；应用内直接导入尚未接入。".to_string(),
            _ => "无法打开 macOS「图像捕捉」应用。".to_string(),
        });
        cx.notify();
    }

    fn refresh_gallery(&mut self, cx: &mut Context<Self>) {
        let Some(folder) = self.source_directory.clone() else {
            self.notice = Some("请先选择要浏览的照片目录。".to_string());
            cx.notify();
            return;
        };
        self.notice = Some("正在刷新图库…".to_string());
        cx.notify();
        cx.spawn(async move |this, cx| {
            let photos = cx
                .background_executor()
                .spawn(async move {
                    let mut photos = Vec::new();
                    collect_media(&folder, &mut photos);
                    photos.sort_by(|a, b| a.file_name().cmp(&b.file_name()));
                    photos
                })
                .await;
            let _ = this.update(cx, |view, cx| {
                let selected_path = view.photos.get(view.selected_media).cloned();
                view.photos = photos;
                view.selected_media = selected_path
                    .and_then(|selected| view.photos.iter().position(|path| path == &selected))
                    .unwrap_or(0);
                view.notice = Some(format!("图库已刷新，共 {} 个项目。", view.photos.len()));
                cx.notify();
            });
        })
        .detach();
    }

    fn scan_duplicates(&mut self, cx: &mut Context<Self>) {
        let Some(folder) = self.source_directory.clone() else {
            self.set_section("重复项", cx);
            self.notice = Some("请先选择要扫描的照片目录。".into());
            return;
        };
        if self.duplicate_scan_running {
            self.set_section("重复项", cx);
            return;
        }
        self.duplicate_scan_running = true;
        let recursive = self.duplicate_scan_recursive;
        self.set_section("重复项", cx);
        self.notice = Some("正在扫描完全相同的照片…".into());
        cx.notify();
        cx.spawn(async move |this, cx| {
            let groups = cx.background_executor().spawn(async move {
                find_duplicate_photos(&folder, recursive)
            }).await;
            let _ = this.update(cx, |view, cx| {
                view.duplicate_groups = groups;
                view.duplicate_keep_paths.clear();
                view.duplicate_selected.clear();
                for (group_index, group) in view.duplicate_groups.iter().enumerate() {
                    if let Some(keeper) = oldest_imported_photo(group) {
                        view.duplicate_keep_paths.insert(group_index, keeper.clone());
                        view.duplicate_selected.extend(group.iter().filter(|path| path.as_path() != keeper.as_path()).cloned());
                    }
                }
                view.duplicate_scan_running = false;
                view.duplicate_scan_completed = true;
                let duplicate_count: usize = view.duplicate_groups.iter().map(Vec::len).sum();
                view.notice = Some(format!("扫描完成：{} 组重复照片，共 {} 张。", view.duplicate_groups.len(), duplicate_count));
                cx.notify();
            });
        }).detach();
    }

    fn set_duplicate_keeper(&mut self, group_index: usize, keeper: PathBuf, cx: &mut Context<Self>) {
        self.duplicate_keep_paths.insert(group_index, keeper.clone());
        if let Some(group) = self.duplicate_groups.get(group_index) {
            for path in group {
                if path == &keeper {
                    self.duplicate_selected.remove(path);
                } else {
                    self.duplicate_selected.insert(path.clone());
                }
            }
        }
        cx.notify();
    }

    fn toggle_duplicate_selection(&mut self, path: PathBuf, cx: &mut Context<Self>) {
        if self.duplicate_selected.contains(&path) {
            self.duplicate_selected.remove(&path);
        } else if !self.duplicate_keep_paths.values().any(|keeper| keeper == &path) {
            self.duplicate_selected.insert(path);
        }
        cx.notify();
    }

    fn toggle_duplicate_group(&mut self, group_index: usize, cx: &mut Context<Self>) {
        let Some(group) = self.duplicate_groups.get(group_index).cloned() else { return };
        let all_selected = group.iter().filter(|path| self.duplicate_keep_paths.get(&group_index) != Some(*path))
            .all(|path| self.duplicate_selected.contains(path));
        for path in group {
            if self.duplicate_keep_paths.get(&group_index) == Some(&path) { continue; }
            if all_selected { self.duplicate_selected.remove(&path); }
            else { self.duplicate_selected.insert(path); }
        }
        cx.notify();
    }

    fn move_selected_duplicates_to_quarantine(&mut self, cx: &mut Context<Self>) {
        let Some(root) = self.source_directory.clone() else { return };
        let selected: Vec<PathBuf> = self.duplicate_selected.iter().cloned().collect();
        if selected.is_empty() {
            self.notice = Some("请先勾选要移入隔离区的副本。".into());
            cx.notify();
            return;
        }
        match quarantine_files(&root, &selected) {
            Ok(moved) => {
                let moved_set: HashSet<PathBuf> = moved.iter().cloned().collect();
                self.photos.retain(|path| !moved_set.contains(path));
                self.duplicate_groups.iter_mut().for_each(|group| group.retain(|path| !moved_set.contains(path)));
                self.duplicate_groups.retain(|group| group.len() > 1);
                self.duplicate_selected.clear();
                self.duplicate_keep_paths.clear();
                for (group_index, group) in self.duplicate_groups.iter().enumerate() {
                    if let Some(keeper) = oldest_imported_photo(group) {
                        self.duplicate_keep_paths.insert(group_index, keeper.clone());
                        self.duplicate_selected.extend(group.iter().filter(|path| path.as_path() != keeper.as_path()).cloned());
                    }
                }
                self.notice = Some(format!("已将 {} 张照片移入隔离区，可随时恢复。", moved_set.len()));
            }
            Err(error) => self.notice = Some(format!("移入隔离区失败：{error}")),
        }
        cx.notify();
    }

    fn restore_quarantined_photos(&mut self, cx: &mut Context<Self>) {
        let Some(root) = self.source_directory.clone() else { return };
        match restore_quarantined_files(&root) {
            Ok(restored) => {
                self.photos.extend(restored.iter().cloned());
                self.photos.sort();
                self.photos.dedup();
                self.notice = Some(format!("已恢复 {} 张照片。", restored.len()));
            }
            Err(error) => self.notice = Some(format!("恢复照片失败：{error}")),
        }
        cx.notify();
    }

    fn render_duplicate_review(&mut self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let group_count = self.duplicate_groups.len();
        let item_count: usize = self.duplicate_groups.iter().map(Vec::len).sum();
        let selected_bytes: u64 = self.duplicate_selected.iter()
            .filter_map(|path| fs::metadata(path).ok().map(|metadata| metadata.len())).sum();

        let mut scope_menu = div().relative().child(button(
            format!("扫描范围：{}  ⌄", if self.duplicate_scan_recursive { "整个图库" } else { "当前文件夹" }), false,
        ).on_click(cx.listener(|this, _, _, cx| {
            this.duplicate_scope_menu_open = !this.duplicate_scope_menu_open;
            cx.notify();
        })));
        if self.duplicate_scope_menu_open {
            let mut menu = div().absolute().top(px(38.)).right_0().w(px(150.)).flex().flex_col().gap_1().p_1()
                .rounded_md().border_1().border_color(rgb(0x505156)).bg(rgb(0x242527));
            for (label, recursive) in [("整个图库", true), ("当前文件夹", false)] {
                menu = menu.child(button(label, self.duplicate_scan_recursive == recursive).w_full().on_click(
                    cx.listener(move |this, _, _, cx| {
                        this.duplicate_scan_recursive = recursive;
                        this.duplicate_scope_menu_open = false;
                        this.scan_duplicates(cx);
                    }),
                ));
            }
            scope_menu = scope_menu.child(deferred(menu).with_priority(100));
        }

        let mut page = div().id("duplicate-review").size_full().flex().flex_col().gap_3().overflow_y_scroll()
            .child(div().flex().items_center().justify_between().child(
                div().flex().flex_col().gap_1()
                    .child(div().text_2xl().font_weight(gpui::FontWeight::SEMIBOLD).text_color(rgb(0xf2f0ec)).child("完全重复项"))
                    .child(div().text_sm().text_color(rgb(0x96979a)).child("按文件内容识别；默认保留创建时间最早的一张，其余副本可批量移入隔离区。")),
            ).child(div().flex().items_center().gap_2().child(scope_menu).child(
                button(if self.duplicate_scan_running { "正在扫描…" } else { "重新扫描" }, true)
                    .on_click(cx.listener(|this, _, _, cx| this.scan_duplicates(cx))),
            )));

        if self.duplicate_scan_running {
            page = page.child(div().p_5().rounded_lg().bg(rgb(0x292a2d)).text_color(rgb(0xb7b5b1)).child("正在逐一校验候选照片内容…"));
        } else if self.duplicate_groups.is_empty() {
            page = page.child(div().p_5().rounded_lg().bg(rgb(0x292a2d)).text_color(rgb(0xb7b5b1)).child(
                if self.source_directory.is_none() { "先选择照片目录，再扫描重复项。" }
                else if !self.duplicate_scan_completed { "尚未扫描，请点击“重新扫描”开始检查。" }
                else { "没有找到内容完全相同的照片。" },
            ));
        } else {
            page = page.child(div().w_full().flex().items_center().gap_5().p_4().rounded_lg().border_1().border_color(rgb(0x414246)).bg(rgb(0x292a2d))
                .child(duplicate_stat(format!("{group_count} 组"), "完全相同"))
                .child(duplicate_stat(format!("{item_count} 项"), "重复照片"))
                .child(duplicate_stat(format_bytes(selected_bytes), "可整理空间"))
                .child(div().flex_1().text_xs().text_color(rgb(0x9b9ca0)).child("每组保留一张。选中的副本会移入可恢复的隔离区。")));

            for (group_index, group) in self.duplicate_groups.clone().into_iter().enumerate() {
                let group_bytes: u64 = group.first().and_then(|path| fs::metadata(path).ok()).map(|metadata| metadata.len()).unwrap_or(0);
                let mut rows = div().flex().flex_col();
                for path in group.iter() {
                    let keeper = self.duplicate_keep_paths.get(&group_index) == Some(path);
                    let selected = self.duplicate_selected.contains(path);
                    let display_path = self.photo_display_path(path, cx);
                    let path_for_keep = path.clone();
                    let path_for_select = path.clone();
                    let name = filename(path);
                    let directory = path.parent().map(|parent| parent.to_string_lossy().to_string()).unwrap_or_default();
                    let row = div().flex().items_center().gap_3().px_4().py_2().border_t_1().border_color(rgb(0x3b3c40))
                        .child(button(if keeper { "◉" } else { "○" }, keeper).on_click(cx.listener(move |this, _, _, cx| {
                            this.set_duplicate_keeper(group_index, path_for_keep.clone(), cx);
                        })))
                        .child(div().size(px(56.)).flex_none().rounded_md().overflow_hidden().bg(rgb(0x3d5c59))
                            .child(img(display_path).size_full().object_fit(ObjectFit::Contain).with_loading(|| image_loading()).with_fallback(|| image_error())))
                        .child(div().flex_1().min_w_0().flex().flex_col().gap_1()
                            .child(div().text_sm().text_color(rgb(0xe5e3df)).child(selectable_media_text(name, path, "duplicate-name")))
                            .child(div().text_xs().text_color(rgb(0x8f9094)).child(selectable_media_text(directory, path, "duplicate-path"))))
                        .child(div().w(px(100.)).text_xs().text_color(rgb(0xa5a6aa)).child(file_size(path)))
                        .child(div().w(px(120.)).text_xs().text_color(rgb(0xa5a6aa)).child(modified_time(path)))
                        .child(button(if keeper { "保留" } else if selected { "移入隔离区" } else { "保留" }, selected)
                            .on_click(cx.listener(move |this, _, _, cx| this.toggle_duplicate_selection(path_for_select.clone(), cx))));
                    rows = rows.child(row);
                }
                let all_selected = group.iter().filter(|path| self.duplicate_keep_paths.get(&group_index) != Some(*path)).all(|path| self.duplicate_selected.contains(path));
                let group_card = div().w_full().rounded_lg().border_1().border_color(rgb(0x414246)).bg(rgb(0x292a2d))
                    .child(div().flex().items_center().justify_between().px_4().py_3().child(
                        div().flex().items_center().gap_2()
                            .child(button(if all_selected { "☑" } else { "☐" }, all_selected).on_click(cx.listener(move |this, _, _, cx| this.toggle_duplicate_group(group_index, cx))))
                            .child(div().text_sm().font_weight(gpui::FontWeight::SEMIBOLD).text_color(rgb(0xe4e2de)).child(format!("重复组 {:02}", group_index + 1)))
                            .child(div().text_xs().text_color(rgb(0x96979a)).child(format!("· 内容完全一致 · {}", format_bytes(group_bytes)))),
                    ).child(div().text_xs().text_color(rgb(0x96979a)).child(format!("可整理 {} 份", group.len().saturating_sub(1)))))
                    .child(rows);
                page = page.child(group_card);
            }
            page = page.child(div().flex().items_center().justify_between().py_2()
                .child(div().text_sm().text_color(rgb(0xa7a8ac)).child(format!("已选择 {} 个副本 · {}", self.duplicate_selected.len(), format_bytes(selected_bytes))))
                .child(div().flex().gap_2()
                    .child(button("取消全选", false).on_click(cx.listener(|this, _, _, cx| { this.duplicate_selected.clear(); cx.notify(); })))
                    .child(button("将所选副本移入隔离区", true).on_click(cx.listener(|this, _, _, cx| this.move_selected_duplicates_to_quarantine(cx))))));
        }
        page.into_any_element()
    }

    fn choose_photo_save_directory(&mut self, cx: &mut Context<Self>) {
        let receiver = cx.prompt_for_paths(PathPromptOptions {
            files: false,
            directories: true,
            multiple: false,
            prompt: Some("选择默认照片保存目录".into()),
        });
        cx.spawn(async move |this, cx| {
            if let Ok(Ok(Some(paths))) = receiver.await
                && let Some(directory) = paths.into_iter().next()
            {
                let save_result = save_photo_directory(&directory);
                let scan_directory = directory.clone();
                let mut photos = cx
                    .background_executor()
                    .spawn(async move {
                        let mut photos = Vec::new();
                        collect_media(&scan_directory, &mut photos);
                        photos.sort_by(|a, b| a.file_name().cmp(&b.file_name()));
                        photos
                    })
                    .await;
                let _ = this.update(cx, |view, cx| {
                    view.photo_save_directory = Some(directory.clone());
                    view.source_directory = Some(directory.clone());
                    let selected_path = view.photos.get(view.selected_media).cloned();
                    view.photos = std::mem::take(&mut photos);
                    view.selected_media = selected_path
                        .and_then(|selected| view.photos.iter().position(|path| path == &selected))
                        .unwrap_or(0);
                    view.notice = Some(match save_result {
                        Ok(()) => format!(
                            "默认目录已更新并加载 {} 个项目；现有文件不会移动。",
                            view.photos.len()
                        ),
                        Err(error) => format!("目录已选中，但设置保存失败：{error}"),
                    });
                    cx.notify();
                });
            }
        })
        .detach();
    }

    fn visible_media(&self) -> Vec<usize> {
        if matches!(self.selected_section.as_str(), "日期未知" | "隔离区" | "删除区域") {
            return Vec::new();
        }
        let mut indices: Vec<_> = if self.selected_section == "重复项" {
            let paths: HashSet<&PathBuf> = self.duplicate_groups.iter().flatten().collect();
            self.photos.iter().enumerate().filter_map(|(index, path)| paths.contains(path).then_some(index)).collect()
        } else if self.categories.contains(&self.selected_section) {
            let paths = self.category_items.get(&self.selected_section);
            self.photos.iter().enumerate().filter_map(|(index, path)| paths.is_some_and(|items| items.contains(path)).then_some(index)).collect()
        } else { (0..self.photos.len())
            .filter(|index| match self.selected_section.as_str() {
                "照片" => is_supported_image(&self.photos[*index]),
                "视频" => is_supported_video(&self.photos[*index]),
                _ => true,
            })
            .collect() };
        match self.sort_mode {
            SortMode::CaptureDate => {
                indices.sort_by_cached_key(|index| self.media_datetime(&self.photos[*index]));
                indices.reverse();
            }
            SortMode::ImportDate => {
                indices.sort_by_key(|index| created_timestamp(&self.photos[*index]));
                indices.reverse();
            }
            SortMode::Filename => {
                indices.sort_by_key(|index| {
                    self.photos[*index]
                        .file_name()
                        .map(|name| name.to_string_lossy().to_lowercase())
                        .unwrap_or_default()
                });
            }
        }
        indices
    }

    fn media_datetime(&self, path: &Path) -> String {
        self.capture_dates
            .get(path)
            .and_then(|date| date.as_ref())
            .cloned()
            .unwrap_or_else(|| modified_time(path))
    }

    fn request_capture_date_reads(&mut self, cx: &mut Context<Self>) {
        let paths: Vec<PathBuf> = self
            .photos
            .iter()
            .filter(|path| is_supported_image(path))
            .filter(|path| {
                !self.capture_dates.contains_key(*path)
                    && !self.capture_date_requests.contains(*path)
            })
            .take(64)
            .cloned()
            .collect();
        if paths.is_empty() {
            return;
        }
        self.capture_date_requests.extend(paths.iter().cloned());
        cx.spawn(async move |this, cx| {
            let dates = cx
                .background_executor()
                .spawn(async move {
                    let mut metadata = paths
                        .into_iter()
                        .map(|path| {
                            let (date, location) = read_exif_metadata(&path);
                            (path, date, location)
                        })
                        .collect::<Vec<_>>();
                    let mut coordinates: Vec<String> = metadata.iter()
                        .filter_map(|(_, _, location)| location.as_deref().map(geocoding_key))
                        .collect();
                    coordinates.sort();
                    coordinates.dedup();
                    let names = reverse_geocode_locations(&coordinates);
                    let names: HashMap<_, _> = coordinates.into_iter().zip(names).collect();
                    metadata.iter_mut().for_each(|(_, _, location)| {
                        if let Some(coordinate) = location.as_ref() {
                            *location = Some(names.get(&geocoding_key(coordinate)).cloned().unwrap_or_else(|| coordinate.clone()));
                        }
                    });
                    metadata
                })
                .await;
            let _ = this.update(cx, |view, cx| {
                for (path, date, location) in dates {
                    view.capture_date_requests.remove(&path);
                    view.capture_dates.insert(path.clone(), date);
                    view.capture_locations.insert(path, location);
                }
                cx.notify();
            });
        })
        .detach();
    }
}

struct PhotoViewer {
    path: PathBuf,
}

struct ResizeGhost;

impl Render for ResizeGhost {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        div().w(px(5.)).h(px(28.)).rounded_full().bg(rgb(0xd1b77d))
    }
}

impl Render for PhotoViewer {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        let path = self.path.clone();
        div()
            .size_full()
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .bg(rgb(0x17181a))
            .child(
                div()
                    .h(px(34.))
                    .flex()
                    .items_center()
                    .text_sm()
                    .text_color(rgb(0xc9c7c3))
                    .child(selectable_media_text(filename(&path), &path, "viewer-name")),
            )
            .child(
                div()
                    .id("photo-canvas")
                    .flex_1()
                    .w_full()
                    .min_w(px(0.))
                    .min_h(px(0.))
                    .overflow_hidden()
                    .flex()
                    .justify_center()
                    .items_center()
                    .child(
                        img(path)
                            .size_full()
                            // Fill the fixed canvas layout box, then fit the source image inside it.
                            .object_fit(ObjectFit::Contain)
                            .with_loading(|| image_loading())
                            .with_fallback(|| image_error()),
                    ),
            )
    }
}

fn collect_media(folder: &Path, media: &mut Vec<PathBuf>) {
    if is_inside_photos_library(folder) {
        return;
    }
    collect_media_recursive(folder, media);
    deduplicate_photos_library_renditions(media);
}

fn collect_media_recursive(folder: &Path, media: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(folder) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        if kind.is_dir() && !is_inside_photos_library(&path)
            && path.file_name().is_none_or(|name| name != ".guangyu-quarantine" && name != ".guangyu-deleted") {
            collect_media_recursive(&path, media);
        } else if kind.is_file() && is_supported_media(&path) {
            media.push(path);
        }
    }
}

fn find_duplicate_photos(folder: &Path, recursive: bool) -> Vec<Vec<PathBuf>> {
    let mut media = Vec::new();
    if recursive {
        collect_media(folder, &mut media);
    } else if let Ok(entries) = fs::read_dir(folder) {
        media.extend(entries.flatten().map(|entry| entry.path()).filter(|path| path.is_file() && is_supported_media(path)));
    }
    let mut by_size = BTreeMap::<u64, Vec<PathBuf>>::new();
    for path in media.into_iter().filter(|path| is_supported_image(path)) {
        if let Ok(metadata) = fs::metadata(&path) {
            by_size.entry(metadata.len()).or_default().push(path);
        }
    }
    let mut by_hash = HashMap::<[u8; 32], Vec<PathBuf>>::new();
    for candidates in by_size.into_values().filter(|paths| paths.len() > 1) {
        for path in candidates {
            let Ok(bytes) = fs::read(&path) else { continue };
            let digest: [u8; 32] = Sha256::digest(&bytes).into();
            by_hash.entry(digest).or_default().push(path);
        }
    }
    let mut groups: Vec<_> = by_hash.into_values().filter(|paths| paths.len() > 1).collect();
    for group in &mut groups {
        group.sort();
    }
    groups.sort_by(|left, right| left[0].cmp(&right[0]));
    groups
}

fn duplicate_stat(value: String, caption: &'static str) -> gpui::Div {
    div().flex().flex_col().gap_1()
        .child(div().text_2xl().font_weight(gpui::FontWeight::SEMIBOLD).text_color(rgb(0xf0eee9)).child(value))
        .child(div().text_xs().text_color(rgb(0x96979a)).child(caption))
}

fn oldest_imported_photo(group: &[PathBuf]) -> Option<PathBuf> {
    group.iter().min_by(|left, right| {
        created_timestamp(left).cmp(&created_timestamp(right)).then_with(|| left.cmp(right))
    }).cloned()
}

fn format_bytes(bytes: u64) -> String {
    const GIB: u64 = 1024 * 1024 * 1024;
    const MIB: u64 = 1024 * 1024;
    if bytes >= GIB { format!("{:.1} GB", bytes as f64 / GIB as f64) }
    else if bytes >= MIB { format!("{:.1} MB", bytes as f64 / MIB as f64) }
    else { format!("{:.0} KB", bytes as f64 / 1024.0) }
}

fn quarantine_files(root: &Path, paths: &[PathBuf]) -> std::io::Result<Vec<PathBuf>> {
    let quarantine_root = root.join(".guangyu-quarantine");
    let mut moved = Vec::new();
    for source in paths {
        let relative = source.strip_prefix(root).map_err(|_| std::io::Error::new(std::io::ErrorKind::InvalidInput, "照片不在当前图库目录中"))?;
        let destination = quarantine_root.join(relative);
        if let Some(parent) = destination.parent() { fs::create_dir_all(parent)?; }
        if destination.exists() {
            return Err(std::io::Error::new(std::io::ErrorKind::AlreadyExists, format!("隔离区中已存在同名文件：{}", destination.display())));
        }
        let thumbnail_cache = photo_thumbnail_cache_path(source);
        fs::rename(source, &destination)?;
        move_photo_thumbnail_cache(thumbnail_cache, &destination);
        moved.push(destination);
    }
    Ok(moved)
}

fn list_quarantined_files(root: &Path) -> Vec<PathBuf> {
    fn visit(folder: &Path, files: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(folder) else { return };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() { visit(&path, files); } else if path.is_file() { files.push(path); }
        }
    }
    let mut files = Vec::new();
    visit(&root.join(".guangyu-quarantine"), &mut files);
    files.sort();
    files
}

fn restore_quarantined_files(root: &Path) -> std::io::Result<Vec<PathBuf>> {
    let quarantine_root = root.join(".guangyu-quarantine");
    let mut restored = Vec::new();
    for quarantined in list_quarantined_files(root) {
        let relative = quarantined.strip_prefix(&quarantine_root).map_err(|_| std::io::Error::new(std::io::ErrorKind::InvalidInput, "隔离区路径无效"))?;
        let destination = root.join(relative);
        if destination.exists() {
            return Err(std::io::Error::new(std::io::ErrorKind::AlreadyExists, format!("原位置已有同名文件，未覆盖：{}", destination.display())));
        }
        if let Some(parent) = destination.parent() { fs::create_dir_all(parent)?; }
        let thumbnail_cache = photo_thumbnail_cache_path(&quarantined);
        fs::rename(&quarantined, &destination)?;
        move_photo_thumbnail_cache(thumbnail_cache, &destination);
        restored.push(destination);
    }
    Ok(restored)
}

fn move_to_deletion_area(root: &Path, source: &Path) -> std::io::Result<PathBuf> {
    let relative = source.strip_prefix(root).map_err(|_| std::io::Error::new(std::io::ErrorKind::InvalidInput, "照片不在当前图库目录中"))?;
    let destination = root.join(".guangyu-deleted").join(relative);
    if let Some(parent) = destination.parent() { fs::create_dir_all(parent)?; }
    if destination.exists() {
        return Err(std::io::Error::new(std::io::ErrorKind::AlreadyExists, format!("删除区域中已存在同名文件：{}", destination.display())));
    }
    let thumbnail_cache = photo_thumbnail_cache_path(source);
    fs::rename(source, &destination)?;
    move_photo_thumbnail_cache(thumbnail_cache, &destination);
    Ok(destination)
}

fn list_deletion_area_files(root: &Path) -> Vec<PathBuf> {
    fn visit(folder: &Path, files: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(folder) else { return };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() { visit(&path, files); } else if path.is_file() { files.push(path); }
        }
    }
    let mut files = Vec::new();
    visit(&root.join(".guangyu-deleted"), &mut files);
    files.sort();
    files
}

fn restore_deletion_area_file(root: &Path, deleted: &Path) -> std::io::Result<PathBuf> {
    let deletion_root = root.join(".guangyu-deleted");
    let relative = deleted.strip_prefix(&deletion_root).map_err(|_| std::io::Error::new(std::io::ErrorKind::InvalidInput, "删除区域路径无效"))?;
    let destination = root.join(relative);
    if destination.exists() {
        return Err(std::io::Error::new(std::io::ErrorKind::AlreadyExists, format!("原位置已有同名文件，未覆盖：{}", destination.display())));
    }
    if let Some(parent) = destination.parent() { fs::create_dir_all(parent)?; }
    let thumbnail_cache = photo_thumbnail_cache_path(deleted);
    fs::rename(deleted, &destination)?;
    move_photo_thumbnail_cache(thumbnail_cache, &destination);
    Ok(destination)
}

fn is_inside_photos_library(path: &Path) -> bool {
    path.components().any(|component| {
        Path::new(component.as_os_str())
            .extension()
            .and_then(|extension| extension.to_str())
            .is_some_and(|extension| extension.eq_ignore_ascii_case("photoslibrary"))
    })
}

fn deduplicate_photos_library_renditions(media: &mut Vec<PathBuf>) {
    let mut preferred = HashMap::<String, (u8, PathBuf)>::new();
    for path in media.iter() {
        let Some((asset_id, priority)) = photos_library_rendition(path) else {
            continue;
        };
        let replace = preferred
            .get(&asset_id)
            .is_none_or(|(best_priority, best_path)| {
                priority < *best_priority
                    || (priority == *best_priority && path.as_os_str() < best_path.as_os_str())
            });
        if replace {
            preferred.insert(asset_id, (priority, path.clone()));
        }
    }
    media.retain(|path| {
        let Some((asset_id, _)) = photos_library_rendition(path) else {
            return true;
        };
        preferred
            .get(&asset_id)
            .is_some_and(|(_, preferred_path)| preferred_path == path)
    });
}

fn photos_library_rendition(path: &Path) -> Option<(String, u8)> {
    if !is_supported_image(path) {
        return None;
    }
    let stem = path.file_stem()?.to_str()?;
    let parts: Vec<&str> = stem.split('_').collect();
    let [asset_id, first, second, variant] = parts.as_slice() else {
        return None;
    };
    let bytes = asset_id.as_bytes();
    if bytes.len() != 36
        || !bytes.iter().enumerate().all(|(index, byte)| {
            if [8, 13, 18, 23].contains(&index) {
                *byte == b'-'
            } else {
                byte.is_ascii_hexdigit()
            }
        })
    {
        return None;
    }
    let priority = match (*first, *second, *variant) {
        ("1", "102", "o") => 0,
        ("1", "102", "c") => 1,
        ("4", "5005", "c") => 2,
        _ => return None,
    };
    Some((asset_id.to_ascii_lowercase(), priority))
}

fn is_supported_media(path: &Path) -> bool {
    is_supported_image(path) || is_supported_video(path)
}

fn is_supported_video(path: &Path) -> bool {
    path.extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| {
            matches!(
                extension.to_ascii_lowercase().as_str(),
                "mov" | "mp4" | "m4v" | "avi" | "mkv" | "wmv" | "3gp"
            )
        })
}

fn live_photo_movie(photo: &Path) -> Option<PathBuf> {
    if !is_supported_image(photo) {
        return None;
    }
    let folder = photo.parent()?;
    let stem = photo.file_stem()?.to_string_lossy();
    ["MOV", "mov", "Mov"].into_iter()
        .map(|extension| folder.join(format!("{stem}.{extension}")))
        .find(|candidate| candidate.is_file() && is_supported_video(candidate))
}

fn format_video_time(seconds: f64) -> String {
    if !seconds.is_finite() || seconds < 0.0 {
        return "00:00".to_string();
    }
    let whole_seconds = seconds as u64;
    format!("{:02}:{:02}", whole_seconds / 60, whole_seconds % 60)
}

fn video_thumbnail_cache_path(source: &Path) -> Option<PathBuf> {
    let metadata = fs::metadata(source).ok()?;
    let modified = metadata
        .modified()
        .ok()?
        .duration_since(std::time::UNIX_EPOCH)
        .ok()?
        .as_secs();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    source.hash(&mut hasher);
    metadata.len().hash(&mut hasher);
    modified.hash(&mut hasher);
    let home = env::var_os("HOME")?;
    Some(
        PathBuf::from(home)
            .join("Library/Caches/Guangyu/VideoThumbnails")
            .join(format!("{:016x}.png", hasher.finish())),
    )
}

fn photo_thumbnail_cache_path(source: &Path) -> Option<PathBuf> {
    let metadata = fs::metadata(source).ok()?;
    let modified = metadata.modified().ok()?.duration_since(std::time::UNIX_EPOCH).ok()?.as_secs();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    source.hash(&mut hasher);
    metadata.len().hash(&mut hasher);
    modified.hash(&mut hasher);
    240_u32.hash(&mut hasher);
    let home = env::var_os("HOME")?;
    Some(PathBuf::from(home).join("Library/Caches/Guangyu/PhotoThumbnails").join(format!("{:016x}.jpg", hasher.finish())))
}

fn photo_thumbnail_cache_path_for_rotation(source: &Path, degrees: u16) -> Option<PathBuf> {
    if degrees == 0 { return photo_thumbnail_cache_path(source); }
    let base = photo_thumbnail_cache_path(source)?;
    let stem = base.file_stem()?.to_string_lossy();
    Some(base.with_file_name(format!("{stem}-rot{degrees}-sips-v2.jpg")))
}

fn generate_photo_thumbnail(source: &Path, display_source: &Path) -> Option<PathBuf> {
    generate_photo_thumbnail_for_rotation(source, display_source, 0)
}

fn generate_photo_thumbnail_for_rotation(source: &Path, display_source: &Path, degrees: u16) -> Option<PathBuf> {
    let destination = photo_thumbnail_cache_path_for_rotation(source, degrees)?;
    if destination.is_file() { return Some(destination); }
    let parent = destination.parent()?;
    fs::create_dir_all(parent).ok()?;
    let stamp = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).ok()?.as_nanos();
    let temporary = destination.with_file_name(format!("{}.tmp-{stamp}.jpg", destination.file_stem()?.to_string_lossy()));
    let mut command = Command::new("/usr/bin/sips");
    if is_heic(display_source) { command.args(["-s", "format", "jpeg"]); }
    let result = command.args(["-Z", "240"]).arg(display_source).arg("--out").arg(&temporary).output().ok()?;
    if !result.status.success() || !temporary.is_file() { return None; }
    fs::rename(&temporary, &destination).ok()?;
    Some(destination)
}

fn generate_rotated_thumbnail_preview(source: &Path, thumbnail: &Path) -> Option<PathBuf> {
    let preview_dir = env::temp_dir().join("guangyu-rotated-thumbnails");
    fs::create_dir_all(&preview_dir).ok()?;
    let stamp = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).ok()?.as_nanos();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    source.hash(&mut hasher);
    stamp.hash(&mut hasher);
    let destination = preview_dir.join(format!("{:016x}.jpg", hasher.finish()));
    let result = Command::new("/usr/bin/sips")
        .arg("-r").arg("90")
        .arg(thumbnail)
        .arg("-o").arg(&destination)
        .output().ok()?;
    (result.status.success() && destination.is_file()).then_some(destination)
}

fn remove_photo_thumbnail_cache(source: &Path) {
    if let Some(path) = photo_thumbnail_cache_path(source) { let _ = fs::remove_file(path); }
}

fn move_photo_thumbnail_cache(source_cache: Option<PathBuf>, destination: &Path) {
    let (Some(source_cache), Some(destination_cache)) = (source_cache, photo_thumbnail_cache_path(destination)) else { return };
    if source_cache.is_file() {
        if let Some(parent) = destination_cache.parent() { let _ = fs::create_dir_all(parent); }
        let _ = fs::rename(source_cache, destination_cache);
    }
}

fn generate_video_thumbnail(source: &Path) -> Option<PathBuf> {
    let destination = video_thumbnail_cache_path(source)?;
    if destination.is_file() {
        return Some(destination);
    }
    let cache_dir = destination.parent()?;
    fs::create_dir_all(cache_dir).ok()?;
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    source.hash(&mut hasher);
    let temporary_dir = cache_dir.join(format!(
        ".tmp-{}-{:016x}",
        std::process::id(),
        hasher.finish()
    ));
    fs::create_dir_all(&temporary_dir).ok()?;
    let result = Command::new("/usr/bin/qlmanage")
        .args(["-t", "-x", "-s", "512", "-o"])
        .arg(&temporary_dir)
        .arg(source)
        .output();
    let generated = if result.is_ok_and(|output| output.status.success()) {
        fs::read_dir(&temporary_dir)
            .ok()?
            .flatten()
            .map(|entry| entry.path())
            .find(|path| path.extension().is_some_and(|extension| extension == "png"))
    } else {
        None
    };
    if let Some(generated) = generated {
        let _ = fs::rename(generated, &destination);
    }
    let _ = fs::remove_dir_all(temporary_dir);
    destination.is_file().then_some(destination)
}

fn is_supported_image(path: &Path) -> bool {
    path.extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| {
            matches!(
                extension.to_ascii_lowercase().as_str(),
                "jpg" | "jpeg" | "png" | "gif" | "webp" | "tif" | "tiff" | "bmp" | "avif" | "heic" | "heif"
            )
        })
}

fn connected_iphone_name() -> Option<String> {
    let output = Command::new("/usr/sbin/ioreg")
        .args(["-p", "IOUSB", "-l", "-w0"])
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&output.stdout);
    text.lines()
        .find(|line| {
            let lower = line.to_lowercase();
            lower.contains("usb product name")
                && (lower.contains("iphone") || lower.contains("apple mobile device"))
        })
        .map(|line| {
            line.rsplit('"')
                .nth(1)
                .filter(|name| !name.is_empty())
                .unwrap_or("iPhone")
                .to_string()
        })
}

fn settings_file() -> Option<PathBuf> {
    env::var_os("HOME").map(|home| {
        PathBuf::from(home)
            .join("Library/Application Support/Guangyu")
            .join("settings.txt")
    })
}

fn load_photo_directory() -> Option<PathBuf> {
    let contents = fs::read_to_string(settings_file()?).ok()?;
    contents
        .lines()
        .find_map(|line| line.strip_prefix("photo_save_directory="))
        .filter(|path| !path.is_empty())
        .map(PathBuf::from)
}

fn category_index_path() -> Option<PathBuf> {
    env::var_os("HOME").map(PathBuf::from).map(|home| home.join("Library/Application Support/Guangyu/categories.idx"))
}

fn diary_index_path() -> Option<PathBuf> {
    env::var_os("HOME").map(PathBuf::from).map(|home| home.join("Library/Application Support/Guangyu/diaries.idx"))
}

fn diary_trash_index_path() -> Option<PathBuf> {
    env::var_os("HOME").map(PathBuf::from).map(|home| home.join("Library/Application Support/Guangyu/diary_trash.idx"))
}

fn load_diaries() -> Vec<DiaryEntry> { load_diary_entries(diary_index_path()) }

fn load_diary_trash() -> Vec<DiaryEntry> { load_diary_entries(diary_trash_index_path()) }

fn load_diary_entries(path: Option<PathBuf>) -> Vec<DiaryEntry> {
    let Some(path) = path else { return Vec::new() };
    let Ok(contents) = fs::read_to_string(path) else { return Vec::new() };
    let mut entries = Vec::new();
    for line in contents.lines().skip(1) {
        let mut fields = line.split('\t');
        let (Some(id), Some(category), Some(title), Some(body), Some(date), Some(photos)) =
            (fields.next(), fields.next(), fields.next(), fields.next(), fields.next(), fields.next()) else { continue };
        let (Ok(id), Some(category), Some(title), Some(body), Some(date)) = (
            id.parse::<u64>(), hex_decode(category).and_then(|v| String::from_utf8(v).ok()),
            hex_decode(title).and_then(|v| String::from_utf8(v).ok()),
            hex_decode(body).and_then(|v| String::from_utf8(v).ok()),
            hex_decode(date).and_then(|v| String::from_utf8(v).ok()),
        ) else { continue };
        let photos = photos.split(',').filter(|photo| !photo.is_empty()).filter_map(hex_decode)
            .filter_map(|v| String::from_utf8(v).ok()).map(PathBuf::from).collect();
        entries.push(DiaryEntry { id, category, title, body, date, photos });
    }
    entries.sort_by(|a, b| b.id.cmp(&a.id));
    entries
}

fn chrono_free_date() -> String {
    Command::new("/bin/date").arg("+%Y年%m月%d日").output().ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string())
        .unwrap_or_else(|| "今天".into())
}

fn save_diaries(entries: &[DiaryEntry]) -> std::io::Result<()> {
    let path = diary_index_path().ok_or_else(|| std::io::Error::new(std::io::ErrorKind::NotFound, "无法确定用户配置目录"))?;
    write_diary_entries(&path, "GUANGYU-DIARIES-1", entries)
}

fn save_diary_trash(entries: &[DiaryEntry]) -> std::io::Result<()> {
    let path = diary_trash_index_path().ok_or_else(|| std::io::Error::new(std::io::ErrorKind::NotFound, "无法确定用户配置目录"))?;
    write_diary_entries(&path, "GUANGYU-DIARY-TRASH-1", entries)
}

fn write_diary_entries(path: &Path, header: &str, entries: &[DiaryEntry]) -> std::io::Result<()> {
    if let Some(parent) = path.parent() { fs::create_dir_all(parent)?; }
    let mut lines = vec![header.to_string()];
    for entry in entries {
        let photos = entry.photos.iter().map(|p| hex_encode(p.to_string_lossy().as_bytes())).collect::<Vec<_>>().join(",");
        lines.push(format!("{}\t{}\t{}\t{}\t{}\t{}", entry.id,
            hex_encode(entry.category.as_bytes()), hex_encode(entry.title.as_bytes()),
            hex_encode(entry.body.as_bytes()), hex_encode(entry.date.as_bytes()), photos));
    }
    fs::write(path, lines.join("\n"))
}

fn prompt_category_name(initial: &str, rename: bool) -> Option<String> {
    let title = if rename { "重命名分类" } else { "新建分类" };
    let script = format!(
        "on run argv\nset result to display dialog \"请输入分类名称\" with title \"{title}\" default answer (item 1 of argv) buttons {{\"取消\", \"确定\"}} default button \"确定\"\nreturn text returned of result\nend run"
    );
    let output = Command::new("/usr/bin/osascript")
        .arg("-e").arg(script).arg(initial)
        .output().ok()?;
    if !output.status.success() { return None; }
    Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes { result.push(HEX[(byte >> 4) as usize] as char); result.push(HEX[(byte & 15) as usize] as char); }
    result
}

fn hex_decode(value: &str) -> Option<Vec<u8>> {
    if value.len() % 2 != 0 { return None; }
    let mut bytes = Vec::with_capacity(value.len() / 2);
    for pair in value.as_bytes().chunks_exact(2) {
        let digit = |byte: u8| match byte { b'0'..=b'9' => Some(byte - b'0'), b'a'..=b'f' => Some(byte - b'a' + 10), b'A'..=b'F' => Some(byte - b'A' + 10), _ => None };
        bytes.push(digit(pair[0])? * 16 + digit(pair[1])?);
    }
    Some(bytes)
}

fn load_category_index() -> (Vec<String>, HashMap<String, HashSet<PathBuf>>) {
    let mut categories = Vec::new();
    let mut items: HashMap<String, HashSet<PathBuf>> = HashMap::new();
    let Some(path) = category_index_path() else { return (categories, items) };
    let Ok(contents) = fs::read_to_string(path) else { return (categories, items) };
    for line in contents.lines().skip(1) {
        let mut parts = line.split('\t');
        match (parts.next(), parts.next(), parts.next()) {
            (Some("C"), Some(name_hex), None) => {
                if let Some(name) = hex_decode(name_hex).and_then(|bytes| String::from_utf8(bytes).ok()) {
                    if !categories.contains(&name) { categories.push(name.clone()); items.entry(name).or_default(); }
                }
            }
            (Some("P"), Some(name_hex), Some(path_hex)) => {
                let name = hex_decode(name_hex).and_then(|bytes| String::from_utf8(bytes).ok());
                let media_path = hex_decode(path_hex).and_then(|bytes| String::from_utf8(bytes).ok()).map(PathBuf::from);
                if let (Some(name), Some(media_path)) = (name, media_path) { items.entry(name).or_default().insert(media_path); }
            }
            _ => {}
        }
    }
    (categories, items)
}

fn save_photo_directory(directory: &Path) -> std::io::Result<()> {
    let path = settings_file()
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::NotFound, "无法确定用户配置目录"))?;
    let parent = path.parent().expect("设置文件应有父目录");
    fs::create_dir_all(parent)?;
    fs::write(
        path,
        format!("photo_save_directory={}\n", directory.display()),
    )
}

fn rotation_settings_file() -> Option<PathBuf> {
    env::var_os("HOME").map(|home| {
        PathBuf::from(home)
            .join("Library/Application Support/Guangyu")
            .join("photo-rotations.txt")
    })
}

fn load_photo_rotations() -> HashMap<PathBuf, u16> {
    let Some(file) = rotation_settings_file() else {
        return HashMap::new();
    };
    let Ok(contents) = fs::read_to_string(file) else {
        return HashMap::new();
    };
    contents
        .lines()
        .filter_map(|line| {
            let (degrees, encoded_path) = line.split_once('\t')?;
            let degrees = degrees.parse::<u16>().ok()?;
            let bytes = (0..encoded_path.len())
                .step_by(2)
                .map(|index| u8::from_str_radix(encoded_path.get(index..index + 2)?, 16).ok())
                .collect::<Option<Vec<_>>>()?;
            let path = String::from_utf8(bytes).ok()?;
            matches!(degrees, 90 | 180 | 270).then_some((PathBuf::from(path), degrees))
        })
        .collect()
}

fn persist_photo_rotations(rotations: &HashMap<PathBuf, u16>) -> std::io::Result<()> {
    let path = rotation_settings_file()
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::NotFound, "无法确定用户配置目录"))?;
    let parent = path.parent().expect("旋转设置文件应有父目录");
    fs::create_dir_all(parent)?;
    let mut entries: Vec<_> = rotations.iter().collect();
    entries.sort_by(|(left, _), (right, _)| left.cmp(right));
    let contents = entries
        .into_iter()
        .map(|(source, degrees)| {
            let encoded = source
                .to_string_lossy()
                .as_bytes()
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>();
            format!("{degrees}\t{encoded}\n")
        })
        .collect::<String>();
    fs::write(path, contents)
}

fn rotated_photo_cache_path(source: &Path, degrees: u16) -> Option<PathBuf> {
    let metadata = fs::metadata(source).ok()?;
    let modified = metadata
        .modified()
        .ok()?
        .duration_since(std::time::UNIX_EPOCH)
        .ok()?
        .as_secs();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    source.hash(&mut hasher);
    metadata.len().hash(&mut hasher);
    modified.hash(&mut hasher);
    degrees.hash(&mut hasher);
    let extension = if is_heic(source) { "jpg".to_string() } else { source.extension()?.to_string_lossy().to_ascii_lowercase() };
    let home = env::var_os("HOME")?;
    Some(
        PathBuf::from(home)
            .join("Library/Caches/Guangyu/RotatedPhotos")
            .join(format!("{:016x}.{extension}", hasher.finish())),
    )
}

fn generate_rotated_photo(source: &Path, degrees: u16) -> Option<PathBuf> {
    let destination = rotated_photo_cache_path(source, degrees)?;
    if destination.is_file() {
        return Some(destination);
    }
    fs::create_dir_all(destination.parent()?).ok()?;
    let mut command = Command::new("/usr/bin/sips");
    if is_heic(source) {
        command.args(["-s", "format", "jpeg"]);
    }
    let result = command.arg("-r")
        .arg(degrees.to_string())
        .arg(source)
        .arg("-o")
        .arg(&destination)
        .output()
        .ok()?;
    (result.status.success() && destination.is_file()).then_some(destination)
}

fn is_heic(path: &Path) -> bool {
    path.extension().and_then(|extension| extension.to_str())
        .is_some_and(|extension| matches!(extension.to_ascii_lowercase().as_str(), "heic" | "heif"))
}

fn heic_preview_cache_path(source: &Path) -> Option<PathBuf> {
    let metadata = fs::metadata(source).ok()?;
    let modified = metadata.modified().ok()?.duration_since(std::time::UNIX_EPOCH).ok()?.as_secs();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    source.hash(&mut hasher);
    metadata.len().hash(&mut hasher);
    modified.hash(&mut hasher);
    Some(PathBuf::from(env::var_os("HOME")?).join("Library/Caches/Guangyu/HeicPreviews").join(format!("{:016x}.jpg", hasher.finish())))
}

fn generate_heic_preview(source: &Path) -> Option<PathBuf> {
    let destination = heic_preview_cache_path(source)?;
    if destination.is_file() { return Some(destination); }
    fs::create_dir_all(destination.parent()?).ok()?;
    let result = Command::new("/usr/bin/sips").args(["-s", "format", "jpeg"])
        .arg(source).arg("--out").arg(&destination).output().ok()?;
    (result.status.success() && destination.is_file()).then_some(destination)
}

fn button(label: impl Into<SharedString>, active: bool) -> gpui::Stateful<gpui::Div> {
    let label = label.into();
    div()
        .id(label.clone())
        .px_3()
        .py_2()
        .rounded_md()
        .text_sm()
        .text_color(if active { rgb(0xf4f3f0) } else { rgb(0xb7b5b1) })
        .bg(if active { rgb(0x383a3d) } else { rgb(0x292a2d) })
        .child(label)
}

fn filename(path: &Path) -> String {
    path.file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| "未命名照片".into())
}

fn truncate_diary_preview(text: &str, available_width: f32, font_size: f32) -> String {
    let width = available_width.max(0.);
    let text_width = |ch: char| if ch.is_ascii() { font_size * 0.56 } else { font_size };
    let measured: f32 = text.chars().map(text_width).sum();
    if measured <= width { return text.to_string(); }
    let ellipsis_width = font_size;
    let limit = (width - ellipsis_width).max(0.);
    let mut result = String::new();
    let mut used = 0.;
    for ch in text.chars() {
        let next = text_width(ch);
        if used + next > limit { break; }
        result.push(ch);
        used += next;
    }
    result.push('…');
    result
}

fn file_size(path: &Path) -> String {
    let Ok(bytes) = fs::metadata(path).map(|metadata| metadata.len()) else {
        return "未知".to_string();
    };
    const UNITS: [&str; 4] = ["B", "KB", "MB", "GB"];
    let mut value = bytes as f64;
    let mut unit = 0;
    while value >= 1024. && unit < UNITS.len() - 1 {
        value /= 1024.;
        unit += 1;
    }
    if unit == 0 {
        format!("{bytes} B")
    } else {
        format!("{value:.1} {}", UNITS[unit])
    }
}

fn image_dimensions(path: &Path) -> Option<String> {
    let file = fs::File::open(path).ok()?;
    let exif = ExifReader::new()
        .read_from_container(&mut BufReader::new(file))
        .ok()?;
    let width = exif
        .get_field(ExifTag::PixelXDimension, ExifIfd::PRIMARY)
        .or_else(|| exif.get_field(ExifTag::ImageWidth, ExifIfd::PRIMARY))?;
    let height = exif
        .get_field(ExifTag::PixelYDimension, ExifIfd::PRIMARY)
        .or_else(|| exif.get_field(ExifTag::ImageLength, ExifIfd::PRIMARY))?;
    Some(format!(
        "{} × {}",
        width.display_value().with_unit(&exif),
        height.display_value().with_unit(&exif)
    ))
}

fn detail_field(label: &'static str, value: String, path: &Path) -> impl IntoElement {
    div()
        .w_full()
        .flex()
        .flex_col()
        .gap_1()
        .pb_3()
        .border_b_1()
        .border_color(rgb(0x414246))
        .child(div().text_xs().text_color(rgb(0x9b9ca0)).child(label))
        .child(div().text_sm().text_color(rgb(0xe2e0dc)).child(selectable_media_text(value, path, label)))
}

fn modified_time(path: &Path) -> String {
    let Ok(modified) = fs::metadata(path).and_then(|metadata| metadata.modified()) else {
        return "未知".to_string();
    };
    let Ok(seconds) = modified.duration_since(std::time::UNIX_EPOCH) else {
        return "未知".to_string();
    };
    let timestamp = seconds.as_secs() as libc::time_t;
    let mut local = unsafe { std::mem::zeroed::<libc::tm>() };
    if unsafe { libc::localtime_r(&timestamp, &mut local) }.is_null() {
        return "未知".to_string();
    }
    format!(
        "{:04}-{:02}-{:02} {:02}:{:02}",
        local.tm_year + 1900,
        local.tm_mon + 1,
        local.tm_mday,
        local.tm_hour,
        local.tm_min
    )
}

fn created_timestamp(path: &Path) -> u64 {
    fs::metadata(path)
        .ok()
        .and_then(|metadata| metadata.created().ok().or_else(|| metadata.modified().ok()))
        .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
        .map(|duration| duration.as_secs())
        .unwrap_or(0)
}

fn read_exif_metadata(path: &Path) -> (Option<String>, Option<String>) {
    let exif = fs::File::open(path).ok().and_then(|file| {
        ExifReader::new()
            .read_from_container(&mut BufReader::new(file))
            .ok()
    });
    let location = exif.as_ref().and_then(|exif| {
        let lat = exif.get_field(ExifTag::GPSLatitude, ExifIfd::PRIMARY)
            .and_then(|field| gps_coordinate(&field.value))?;
        let lon = exif.get_field(ExifTag::GPSLongitude, ExifIfd::PRIMARY)
            .and_then(|field| gps_coordinate(&field.value))?;
        let lat_ref = exif.get_field(ExifTag::GPSLatitudeRef, ExifIfd::PRIMARY)
            .map(|field| field.display_value().to_string());
        let lon_ref = exif.get_field(ExifTag::GPSLongitudeRef, ExifIfd::PRIMARY)
            .map(|field| field.display_value().to_string());
        let lat = if lat_ref.as_deref().is_some_and(|value| value.starts_with('S')) { -lat } else { lat };
        let lon = if lon_ref.as_deref().is_some_and(|value| value.starts_with('W')) { -lon } else { lon };
        Some(format!("{lat:.4}, {lon:.4}"))
    }).or_else(|| read_macos_gps_metadata(path));
    let mut capture_date = None;
    for tag in [
        ExifTag::DateTimeOriginal,
        ExifTag::DateTimeDigitized,
        ExifTag::DateTime,
    ] {
        // In kamadak-exif, the EXIF sub-IFD is index 2.
        let Some(field) = exif.as_ref().and_then(|exif| exif.get_field(tag, ExifIfd::PRIMARY)) else {
            continue;
        };
        let ExifValue::Ascii(values) = &field.value else {
            continue;
        };
        let Some(raw) = values.first() else {
            continue;
        };
        let Ok(datetime) = exif::DateTime::from_ascii(raw) else {
            continue;
        };
        if datetime.year > 0
            && (1..=12).contains(&datetime.month)
            && (1..=31).contains(&datetime.day)
            && datetime.hour <= 23
            && datetime.minute <= 59
            && datetime.second <= 60
        {
            capture_date = Some(datetime.to_string());
            break;
        }
    }
    let capture_date = capture_date.or_else(|| read_macos_capture_datetime(path));
    (capture_date, location)
}

fn diary_photo_capture_info(path: &Path) -> Vec<String> {
    let (capture_date, location) = read_exif_metadata(path);
    let exif = fs::File::open(path).ok().and_then(|file| {
        ExifReader::new()
            .read_from_container(&mut BufReader::new(file))
            .ok()
    });
    let mut details = Vec::new();
    if let Some(date) = capture_date {
        details.push(format!("拍摄时间：{date}"));
    }
    if let Some(location) = location {
        details.push(format!("拍摄地点：{location}"));
    }
    if let Some(exif) = exif.as_ref() {
        let value = |tag| exif.get_field(tag, ExifIfd::PRIMARY)
            .map(|field| field.display_value().with_unit(exif).to_string())
            .map(|text| text.trim().trim_matches('"').to_string())
            .filter(|text| !text.is_empty());
        let camera = [value(ExifTag::Make), value(ExifTag::Model)]
            .into_iter().flatten().collect::<Vec<_>>().join(" ");
        if !camera.is_empty() {
            details.push(format!("相机：{camera}"));
        }
        if let Some(lens) = value(ExifTag::LensModel) {
            details.push(format!("镜头：{lens}"));
        }
        let mut settings = Vec::new();
        if let Some(aperture) = value(ExifTag::FNumber) { settings.push(aperture); }
        if let Some(exposure) = value(ExifTag::ExposureTime) { settings.push(exposure); }
        if let Some(iso) = value(ExifTag::PhotographicSensitivity) { settings.push(format!("ISO {iso}")); }
        if let Some(focal_length) = value(ExifTag::FocalLength) { settings.push(focal_length); }
        if !settings.is_empty() {
            details.push(format!("拍摄参数：{}", settings.join(" · ")));
        }
    }
    if details.is_empty() {
        details.push("未包含拍摄信息".to_string());
    }
    details
}

fn read_macos_capture_datetime(path: &Path) -> Option<String> {
    let output = Command::new("/usr/bin/mdls")
        .args(["-raw", "-name", "kMDItemContentCreationDate"])
        .arg(path)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let raw = String::from_utf8_lossy(&output.stdout);
    let parts: Vec<_> = raw.split_whitespace().collect();
    let [date, time, zone] = parts.as_slice() else { return None };
    let mut date_parts = date.split('-').filter_map(|part| part.parse::<i32>().ok());
    let (year, month, day) = (date_parts.next()?, date_parts.next()?, date_parts.next()?);
    let mut time_parts = time.split(':').filter_map(|part| part.parse::<i32>().ok());
    let (hour, minute, second) = (time_parts.next()?, time_parts.next()?, time_parts.next()?);
    if !(1..=12).contains(&month) || !(1..=31).contains(&day)
        || !(0..=23).contains(&hour) || !(0..=59).contains(&minute) || !(0..=60).contains(&second) {
        return None;
    }
    let zone = zone.as_bytes();
    if zone.len() != 5 || !matches!(zone[0], b'+' | b'-') {
        return None;
    }
    let zone_hours = std::str::from_utf8(&zone[1..3]).ok()?.parse::<i64>().ok()?;
    let zone_minutes = std::str::from_utf8(&zone[3..5]).ok()?.parse::<i64>().ok()?;
    let direction = if zone[0] == b'-' { -1 } else { 1 };
    let offset = direction * (zone_hours * 3600 + zone_minutes * 60);
    let mut utc = libc::tm {
        tm_year: year - 1900,
        tm_mon: month - 1,
        tm_mday: day,
        tm_hour: hour,
        tm_min: minute,
        tm_sec: second,
        ..unsafe { std::mem::zeroed() }
    };
    let timestamp = unsafe { libc::timegm(&mut utc) } - offset;
    let mut local = unsafe { std::mem::zeroed::<libc::tm>() };
    if unsafe { libc::localtime_r(&timestamp, &mut local) }.is_null() {
        return None;
    }
    Some(format!("{:04}:{:02}:{:02} {:02}:{:02}:{:02}",
        local.tm_year + 1900, local.tm_mon + 1, local.tm_mday,
        local.tm_hour, local.tm_min, local.tm_sec))
}

fn gps_coordinate(value: &ExifValue) -> Option<f64> {
    let ExifValue::Rational(values) = value else { return None };
    if values.len() < 3 { return None; }
    let d = values[0].to_f64();
    let m = values[1].to_f64();
    let s = values[2].to_f64();
    Some(d + m / 60. + s / 3600.)
}

fn read_macos_gps_metadata(path: &Path) -> Option<String> {
    let output = Command::new("/usr/bin/mdls")
        .args(["-raw", "-name", "kMDItemLatitude", "-name", "kMDItemLongitude"])
        .arg(path)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let output_text = String::from_utf8_lossy(&output.stdout);
    let values: Vec<_> = output_text
        .split('\0')
        .map(str::trim)
        .collect();
    let lat = values.first()?.parse::<f64>().ok()?;
    let lon = values.get(1)?.parse::<f64>().ok()?;
    if !(-90.0..=90.0).contains(&lat) || !(-180.0..=180.0).contains(&lon) {
        return None;
    }
    Some(format!("{lat:.4}, {lon:.4}"))
}

fn reverse_geocode_locations(coordinates: &[String]) -> Vec<String> {
    if coordinates.is_empty() {
        return Vec::new();
    }
    const SCRIPT: &str = r#"
import Foundation
import MapKit
let coordinates = Array(CommandLine.arguments.dropFirst())
Task { @MainActor in
    for value in coordinates {
        let pair = value.split(separator: ",").compactMap { Double($0.trimmingCharacters(in: .whitespaces)) }
        guard pair.count == 2,
              let request = MKReverseGeocodingRequest(location: CLLocation(latitude: pair[0], longitude: pair[1])) else {
            print(value)
            continue
        }
        request.preferredLocale = Locale(identifier: "zh_CN")
        do {
            let items = try await request.mapItems
            let address = items.first?.addressRepresentations?.fullAddress(includingRegion: false, singleLine: true)
            print(address ?? items.first?.name ?? value)
        } catch {
            print(value)
        }
    }
    exit(0)
}

dispatchMain()
"#;
    let output = Command::new("/usr/bin/swift")
        .arg("-e")
        .arg(SCRIPT)
        .args(coordinates)
        .output();
    let Ok(output) = output else {
        return coordinates.to_vec();
    };
    if !output.status.success() {
        return coordinates.to_vec();
    }
    let resolved: Vec<String> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect();
    if resolved.len() == coordinates.len() { resolved } else { coordinates.to_vec() }
}

fn geocoding_key(coordinate: &str) -> String {
    let mut parts = coordinate.split(',').map(str::trim);
    match (parts.next().and_then(|part| part.parse::<f64>().ok()),
           parts.next().and_then(|part| part.parse::<f64>().ok())) {
        (Some(latitude), Some(longitude)) => format!("{latitude:.3}, {longitude:.3}"),
        _ => coordinate.to_string(),
    }
}

fn file_kind(path: &Path) -> String {
    let extension = path
        .extension()
        .and_then(|extension| extension.to_str())
        .unwrap_or("")
        .to_ascii_lowercase();
    match extension.as_str() {
        "jpg" | "jpeg" => "JPEG 图像".to_string(),
        "png" => "PNG 图像".to_string(),
        "gif" => "GIF 图像".to_string(),
        "webp" => "WebP 图像".to_string(),
        "tif" | "tiff" => "TIFF 图像".to_string(),
        "bmp" => "BMP 图像".to_string(),
        "avif" => "AVIF 图像".to_string(),
        "heic" | "heif" => "HEIF 图像".to_string(),
        "mov" => "QuickTime 影片".to_string(),
        "mp4" | "m4v" => "MPEG-4 影片".to_string(),
        "avi" => "AVI 影片".to_string(),
        "mkv" => "Matroska 影片".to_string(),
        "wmv" => "WMV 影片".to_string(),
        "3gp" => "3GPP 影片".to_string(),
        _ => "图像文件".to_string(),
    }
}

fn media_thumbnail(path: &Path, thumbnail: Option<PathBuf>, failed: bool) -> gpui::AnyElement {
    if is_supported_video(path) {
        if let Some(thumbnail) = thumbnail {
            img(thumbnail)
                .size_full()
                .object_fit(ObjectFit::Cover)
                .into_any_element()
        } else {
            div()
                .size_full()
                .flex()
                .flex_col()
                .justify_center()
                .items_center()
                .gap_2()
                .bg(rgb(0x303236))
                .text_color(rgb(0xd8d6d2))
                .child("▶")
                .child(if failed {
                    "无法生成视频预览图"
                } else {
                    "正在生成视频预览图…"
                })
                .into_any_element()
        }
    } else {
        img(thumbnail.unwrap_or_else(|| path.to_path_buf()))
            .size_full()
            .object_fit(ObjectFit::Contain)
            .with_loading(|| image_loading())
            .with_fallback(|| image_error())
            .into_any_element()
    }
}

fn media_preview(
    path: &Path,
    display_path: &Path,
    thumbnail: Option<PathBuf>,
    failed: bool,
    video_frame: Option<core_video::pixel_buffer::CVPixelBuffer>,
) -> gpui::AnyElement {
    if is_supported_video(path) {
        if let Some(frame) = video_frame {
            surface(frame)
                .size_full()
                .object_fit(ObjectFit::Contain)
                .into_any_element()
        } else if let Some(thumbnail) = thumbnail {
            img(thumbnail)
                .size_full()
                .object_fit(ObjectFit::Contain)
                .into_any_element()
        } else {
            div()
                .size_full()
                .flex()
                .flex_col()
                .justify_center()
                .items_center()
                .gap_3()
                .bg(rgb(0x202124))
                .text_color(rgb(0xd8d6d2))
                .child(div().text_2xl().child("▶"))
                .child(if failed {
                    "无法生成视频预览图"
                } else {
                    "正在生成视频预览图…"
                })
                .into_any_element()
        }
    } else {
        div()
            .size_full()
            .min_w(px(0.))
            .min_h(px(0.))
            .flex()
            .justify_center()
            .items_center()
            .child(
                img(display_path.to_path_buf())
                    .size_full()
                    .object_fit(ObjectFit::Contain)
                    .with_loading(|| image_loading())
                    .with_fallback(|| image_error()),
            )
            .into_any_element()
    }
}

impl Render for PhotoApp {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        self.request_capture_date_reads(cx);
        if (self.view_mode != ViewMode::Gallery || self.selected_section == "设置")
            && let Some(playback) = &mut self.video_playback
            && playback.playing
        {
            unsafe { playback.player.pause() };
            playback.playing = false;
        }
        if !self.device_polling_started {
            self.device_polling_started = true;
            let entity = cx.entity();
            cx.spawn(async move |_this, async_cx| {
                let mut first_scan = true;
                loop {
                    if first_scan {
                        first_scan = false;
                    } else {
                        async_cx
                            .background_executor()
                            .timer(Duration::from_secs(5))
                            .await;
                    }
                    let connected = async_cx
                        .background_executor()
                        .spawn(async { connected_iphone_name() })
                        .await;
                    let source_directory = async_cx
                        .update(|app| entity.read(app).source_directory.clone())
                        .ok()
                        .flatten();
                    let refreshed_photos = if let Some(directory) = source_directory.clone() {
                        async_cx
                            .background_executor()
                            .spawn(async move {
                                let mut photos = Vec::new();
                                collect_media(&directory, &mut photos);
                                photos.sort_by(|a, b| a.file_name().cmp(&b.file_name()));
                                photos
                            })
                            .await
                    } else {
                        Vec::new()
                    };
                    if async_cx
                        .update(|app| {
                            entity.update(app, |view, cx| {
                                let mut changed = false;
                                if view.connected_iphone != connected {
                                    view.connected_iphone = connected;
                                    changed = true;
                                }
                                if source_directory.is_some()
                                    && view.source_directory == source_directory
                                    && view.photos != refreshed_photos
                                {
                                    let selected_path =
                                        view.photos.get(view.selected_media).cloned();
                                    view.photos = refreshed_photos;
                                    view.selected_media = selected_path
                                        .and_then(|selected| {
                                            view.photos.iter().position(|path| path == &selected)
                                        })
                                        .unwrap_or(0);
                                    view.notice = Some(format!(
                                        "图库已自动刷新，共 {} 个项目。",
                                        view.photos.len()
                                    ));
                                    changed = true;
                                }
                                if changed {
                                    cx.notify();
                                }
                            })
                        })
                        .is_err()
                    {
                        break;
                    }
                }
            })
            .detach();
        }
        let photo_count = self
            .photos
            .iter()
            .filter(|path| is_supported_image(path))
            .count()
            .to_string();
        let video_count = self
            .photos
            .iter()
            .filter(|path| is_supported_video(path))
            .count()
            .to_string();
        let all_media_count = self.photos.len().to_string();
        let nav_items = [
            ("所有照片", all_media_count),
            ("导入", String::new()),
            ("重复项", format!("{} 组", self.duplicate_groups.len())),
            ("隔离区", self.source_directory.as_deref().map(|root| list_quarantined_files(root).len().to_string()).unwrap_or_else(|| "0".into())),
            ("照片", photo_count),
            ("视频", video_count),
            ("日期未知", self.photos.iter().filter(|path| self.capture_dates.get(*path).is_some_and(|date| date.is_none())).count().to_string()),
            ("删除区域", self.source_directory.as_deref().map(|root| list_deletion_area_files(root).len().to_string()).unwrap_or_else(|| "0".into())),
        ];
        let mut sidebar = div()
            .id("sidebar")
            .w(px(220.))
            .min_w(px(220.))
            .flex_none()
            .h_full()
            .flex()
            .flex_col()
            .overflow_y_scroll()
            .gap_1()
            .p_3()
            .border_r_1()
            .border_color(rgb(0x38393c))
            .bg(rgb(0x242527))
            .child(
                div()
                    .mb_2()
                    .flex()
                    .items_center()
                    .gap_2()
                    .px_2()
                    .py_1()
                    .child(div().w(px(8.)).h(px(8.)).rounded_full().bg(rgb(0x64b883)))
                    .child(
                        div()
                            .text_sm()
                            .font_weight(gpui::FontWeight::SEMIBOLD)
                            .text_color(rgb(0xf5f3ef))
                            .child("家庭照片图库"),
                    ),
            );
        sidebar = sidebar.child(
            div()
                .mb_3()
                .flex()
                .flex_col()
                .gap_2()
                .p_3()
                .rounded_lg()
                .border_1()
                .border_color(rgb(0x3a3b3e))
                .bg(rgb(0x2b2c2f))
                .child(div().text_xs().text_color(rgb(0x929398)).child("当前图库"))
                .child(
                    div()
                        .flex()
                        .items_center()
                        .gap_2()
                        .text_sm()
                        .font_weight(gpui::FontWeight::MEDIUM)
                        .text_color(rgb(0xe8e7e4))
                        .child(div().w(px(7.)).h(px(7.)).rounded_full().bg(rgb(0x59b77c)))
                        .child("家庭照片图库"),
                )
                .child(
                    div().text_xs().text_color(rgb(0x999a9e)).child(
                        self.source_directory
                            .as_ref()
                            .map(|p| p.display().to_string())
                            .unwrap_or_else(|| "选择照片目录开始".into()),
                    ),
                ),
        );
        sidebar = sidebar.child(
            div()
                .px_2()
                .py_2()
                .text_xs()
                .font_weight(gpui::FontWeight::MEDIUM)
                .text_color(rgb(0x8e9094))
                .child("图库"),
        );

        sidebar = sidebar.child(button(format!("▤  日记   {} 篇", self.diaries.len()), self.diary_column_open)
            .w_full().on_click(cx.listener(|this, _, _, cx| this.toggle_diary_column(cx))));

        for (label, count) in nav_items {
            if label == "照片" || label == "删除区域" {
                let heading = if label == "照片" { "媒体类型" } else { "回收" };
                sidebar = sidebar.child(
                    div()
                        .mt_3()
                        .px_2()
                        .py_2()
                        .text_xs()
                        .font_weight(gpui::FontWeight::MEDIUM)
                        .text_color(rgb(0x8e9094))
                        .child(heading),
                );
            }
            let active = self.selected_section == label
                || (label == "所有照片" && self.selected_section == "图库");
            let target = label.to_string();
            let mut nav_item = div()
                    .id(SharedString::from(label))
                    .relative()
                    .flex()
                    .justify_between()
                    .items_center()
                    .px_3()
                    .py_2()
                    .rounded_md()
                    .text_sm()
                    .text_color(if active { rgb(0x91b4ff) } else { rgb(0xd0cfcc) })
                    .bg(if active { rgb(0x35436a) } else { rgb(0x242527) })
                    .child(
                        div()
                            .flex()
                            .items_center()
                            .gap_3()
                            .child(
                                div()
                                    .w(px(14.))
                                    .text_color(if active { rgb(0x91b4ff) } else { rgb(0x929398) })
                                    .child(match label {
                                        "所有照片" => "▦",
                                        "导入" => "↓",
                                        "重复项" => "◉",
                                        "隔离区" => "▱",
                                        "删除区域" => "⌫",
                                        "照片" => "▧",
                                        "视频" => "▷",
                                        _ => "◷",
                                    }),
                            )
                            .child(div().min_w(px(0.)).flex_1().text_ellipsis().child(label)),
                    )
                    .child(div().flex_none().text_xs().text_color(rgb(0xa4a5a9)).child(count));
            nav_item = nav_item.drag_over::<MediaDrag>(move |style, _, _, _| {
                style.bg(if label == "删除区域" { rgb(0x5a4148) } else { rgb(0x465a83) })
                    .border_1()
                    .border_color(if label == "删除区域" { rgb(0xf08b94) } else { rgb(0x91b4ff) })
            });
            if label == "隔离区" {
                nav_item = nav_item
                    .on_drop(cx.listener(|this, drag: &MediaDrag, window, cx| {
                        let position = window.mouse_position();
                        this.move_dragged_to_quarantine(&drag.path, drag.source_category.as_deref(), (position.x.to_f64() as f32, position.y.to_f64() as f32), cx)
                    }));
            } else if label == "删除区域" {
                nav_item = nav_item
                    .on_drop(cx.listener(|this, drag: &MediaDrag, window, cx| {
                        let position = window.mouse_position();
                        this.move_dragged_to_deletion_area(&drag.path, drag.source_category.as_deref(), (position.x.to_f64() as f32, position.y.to_f64() as f32), cx)
                    }));
            } else {
                nav_item = nav_item.on_drop(cx.listener(move |this, drag: &MediaDrag, window, cx| {
                    if let Some(category) = drag.source_category.as_deref() {
                        let position = window.mouse_position();
                        this.remove_paths_from_category(category, &drag.paths, (position.x.to_f64() as f32, position.y.to_f64() as f32), cx);
                    }
                }));
            }
            sidebar = sidebar.child(nav_item
                    .on_click(cx.listener(move |this, _, _, cx| {
                        if target == "导入" {
                            this.open_image_capture(cx);
                        } else {
                            this.set_section(
                                if target == "所有照片" {
                                    "图库"
                                } else {
                                    &target
                                },
                                cx,
                            );
                        }
                    })));
            if label == "删除区域" {
                sidebar = sidebar.child(button(format!("▱  日记回收站   {}", self.diary_trash.len()), self.selected_section == "日记回收站")
                    .w_full().on_click(cx.listener(|this, _, _, cx| this.set_section("日记回收站", cx))));
            }
        }
        sidebar = sidebar.child(
            div()
                .mt_3()
                .px_2()
                .flex()
                .justify_between()
                .items_center()
                .child(
                    div()
                        .text_xs()
                        .text_color(rgb(0x8e9094))
                        .child("自定义分类"),
                )
                .child(button("＋", false).on_click(cx.listener(|this, _, _, cx| {
                    this.add_category(cx);
                }))),
        );
        for name in self.categories.clone() {
            let active = self.selected_section == name;
            let target = name.clone();
            let drop_target = name.clone();
            let count = self.category_items.get(&name).map(HashSet::len).unwrap_or(0);
            sidebar = sidebar.child(
                button(format!("▦  {name}  {count}"), active).w_full()
                    .drag_over::<MediaDrag>(|style, _, _, _| style.bg(rgb(0x465a83)).border_1().border_color(rgb(0x91b4ff)))
                    .on_drop(cx.listener(move |this, drag: &MediaDrag, _, cx| this.add_paths_to_category(&drop_target, &drag.paths, cx)))
                    .on_click(cx.listener(move |this, _, _, cx| this.set_section(&target, cx))),
            );
        }
        if self.categories.contains(&self.selected_section) {
            let source_category = self.selected_section.clone();
            sidebar = sidebar.child(
                button("↗  从此分类移出所选", false).w_full()
                    .drag_over::<MediaDrag>(|style, _, _, _| style.bg(rgb(0x5a4148)).border_1().border_color(rgb(0xf08b94)))
                    .on_drop(cx.listener(move |this, drag: &MediaDrag, window, cx| {
                        let position = window.mouse_position();
                        let paths = if drag.paths.is_empty() { vec![drag.path.clone()] } else { drag.paths.clone() };
                        this.remove_paths_from_category(&source_category, &paths, (position.x.to_f64() as f32, position.y.to_f64() as f32), cx);
                    }))
            );
        }
        sidebar = sidebar.child(button("＋  管理分类", self.selected_section == "管理分类").w_full().on_click(
            cx.listener(|this, _, _, cx| this.set_section("管理分类", cx)),
        ));
        if let Some(device_name) = self.connected_iphone.clone() {
            sidebar = sidebar.child(
                div()
                    .flex()
                    .flex_col()
                    .gap_2()
                    .p_3()
                    .rounded_md()
                    .bg(rgb(0x292a2d))
                    .text_sm()
                    .text_color(rgb(0xd8d6d2))
                    .child(format!("📱 {device_name}"))
                    .child(
                        button("打开图像捕捉…", false)
                            .on_click(cx.listener(|this, _, _, cx| this.open_image_capture(cx))),
                    ),
            );
        } else {
            sidebar = sidebar.child(
                div()
                    .px_2()
                    .py_2()
                    .text_xs()
                    .text_color(rgb(0x777a7e))
                    .child("未检测到 iPhone"),
            );
        }
        sidebar = sidebar.child(div().flex_1());
        sidebar = sidebar.child(
            div()
                .flex()
                .items_center()
                .justify_between()
                .px_2()
                .py_1()
                .text_xs()
                .text_color(rgb(0x999a9e))
                .child("图库空间")
                .child("184.6 / 500 GB"),
        );
        sidebar = sidebar.child(
            div()
                .mx_2()
                .mb_2()
                .h(px(4.))
                .rounded_full()
                .bg(rgb(0x45464a))
                .child(div().w(px(110.)).h_full().rounded_full().bg(rgb(0x8daeff))),
        );
        sidebar = sidebar.child(
            button("设置", self.selected_section == "设置")
                .on_click(cx.listener(|this, _, _, cx| this.set_section("设置", cx))),
        );

        let modes = [
            (ViewMode::Names, "☷"),
            (ViewMode::Small, "▤"),
            (ViewMode::Large, "▦"),
            (ViewMode::Gallery, "▣"),
        ];
        let mut mode_controls = div().flex().gap_1();
        for (mode, icon) in modes {
            let active = self.view_mode == mode;
            mode_controls = mode_controls.child(
                button(icon, active)
                    .on_click(cx.listener(move |this, _, _, cx| this.set_mode(mode, cx))),
            );
        }

        let media = self.visible_media();
        self.selection_display_order = media.clone();
        let section_title = if self.selected_section == "图库" {
            "所有照片".to_string()
        } else {
            self.selected_section.clone()
        };
        let directory_label = self
            .source_directory
            .as_ref()
            .map(|path| path.display().to_string())
            .unwrap_or_else(|| "选择一个照片目录开始浏览".into());
        let header_subtitle = if self.selected_section == "日记回收站" {
            "删除的日记会暂存在这里，可恢复或彻底删除".to_string()
        } else if self.selected_section == "设置" {
            "管理照片保存目录与应用信息".to_string()
        } else if self.selected_section == "管理分类" {
            "分类只保存索引关系，不改变照片文件位置".to_string()
        } else {
            format!("{} 项 · 最近导入 · {}", media.len(), directory_label)
        };
        let mut header = div().flex().justify_between().items_center().mb_5().child(
            div()
                .flex()
                .flex_col()
                .gap_1()
                .child(
                    div()
                        .text_2xl()
                        .font_weight(gpui::FontWeight::SEMIBOLD)
                        .text_color(rgb(0xf2f0ec))
                        .child(section_title),
                )
                .child(
                    div()
                        .text_sm()
                        .text_color(rgb(0x96979a))
                        .child(header_subtitle),
                ),
        );
        if self.selected_section == "管理分类" {
            header = header.child(button("＋ 新建分类", true).on_click(cx.listener(|this, _, _, cx| this.add_category(cx))));
        } else if self.categories.contains(&self.selected_section) {
            let category = self.selected_section.clone();
            header = header.child(button("＋ 添加所选照片", true).on_click(cx.listener(move |this, _, _, cx| this.add_selected_to_category(&category, cx))));
        }
        if let Some(notice) = self.notice.clone() {
            header = header.child(div().text_xs().text_color(rgb(0xc9b68c)).child(notice));
        }

        let sort_label = match self.sort_mode {
            SortMode::CaptureDate => "拍摄日期：最新优先",
            SortMode::ImportDate => "导入日期：最新优先",
            SortMode::Filename => "文件名：A–Z",
        };
        let mut sort_control = div().relative().id("sort-control").child(
            button(format!("{sort_label}  ⌄"), false).on_click(cx.listener(|this, _, _, cx| {
                this.sort_menu_open = !this.sort_menu_open;
                cx.notify();
            })),
        );
        if self.sort_menu_open {
            let options = [
                ("拍摄日期：最新优先", SortMode::CaptureDate),
                ("导入日期：最新优先", SortMode::ImportDate),
                ("文件名：A–Z", SortMode::Filename),
            ];
            let mut menu = div()
                .absolute()
                .id("sort-menu")
                .top(px(34.))
                .left_0()
                .w(px(190.))
                .flex()
                .flex_col()
                .gap_1()
                .p_1()
                .rounded_md()
                .border_1()
                .border_color(rgb(0x505156))
                .bg(rgb(0x242527));
            for (label, mode) in options {
                menu = menu.child(button(label, self.sort_mode == mode).w_full().on_click(
                    cx.listener(move |this, _, _, cx| {
                        this.set_sort_mode(mode, cx);
                    }),
                ));
            }
            sort_control = sort_control.child(deferred(menu).with_priority(100));
        }
        let mut toolbar = div()
            .flex()
            .items_center()
            .gap_2()
            .mb_4()
            .pb_3()
            .border_b_1()
            .border_color(rgb(0x38393c))
            .child(
                div()
                    .flex_1()
                    .text_xs()
                    .text_color(rgb(0xaaa9ad))
                    .child("⌕  搜索照片"),
            )
            .child(sort_control)
            .child(button(format!("多选 {}", self.selected_paths.len()), false).on_click(cx.listener(|this, _, _, cx| {
                if this.selected_paths.is_empty() {
                    if let Some(path) = this.photos.get(this.selected_media) { this.selected_paths.insert(path.clone()); }
                } else { this.selected_paths.clear(); }
                cx.notify();
            })))
            .child(button("拷贝所选", false).on_click(cx.listener(|this, _, _, cx| { this.copy_selected_photos(); cx.notify(); })))
            .child(button("移至删除区域", false).on_click(cx.listener(|this, _, _, cx| this.delete_selected_photos(cx))))
            .child(
                button(if self.duplicate_scan_running { "正在扫描…" } else { "扫描重复项" }, false)
                    .on_click(cx.listener(|this, _, _, cx| this.scan_duplicates(cx))),
            )
            .child(mode_controls);
        toolbar = toolbar.child(button("＋ 导入", true).on_click(cx.listener(|this, _, _, cx| this.open_image_capture(cx))));

        let content = if self.selected_section == "管理分类" {
            let mut rows = div().w_full().flex().flex_col().rounded_lg().border_1().border_color(rgb(0x414247)).bg(rgb(0x292a2d));
            for (index, name) in self.categories.clone().into_iter().enumerate() {
                let count = self.category_items.get(&name).map(HashSet::len).unwrap_or(0);
                let rename_name = name.clone();
                let delete_name = name.clone();
                let row = div().w_full().flex().items_center().justify_between().px_4().py_3()
                    .border_b_1().border_color(rgb(0x414247))
                    .child(div().flex().items_center().gap_3().text_sm().text_color(rgb(0xe5e3df))
                        .child("▦").child(name.clone()))
                    .child(div().flex().items_center().gap_2()
                        .child(div().mr_2().text_xs().text_color(rgb(0x999a9e)).child(format!("{count} 张照片")))
                        .child(button("重命名", false).on_click(cx.listener(move |this, _, _, cx| this.rename_category(&rename_name, cx))))
                        .child(button("删除分类", false).on_click(cx.listener(move |this, _, _, cx| this.delete_category(&delete_name, cx)))));
                rows = rows.child(if index + 1 == self.categories.len() { row.border_b_0() } else { row });
            }
            div().size_full().flex().flex_col().gap_2().child(rows)
                .child(div().text_xs().text_color(rgb(0x929398)).child("删除分类只移除分类索引，不会删除照片。"))
                .into_any_element()
        } else if self.selected_section == "设置" {
            let save_directory = self
                .photo_save_directory
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "尚未设置".to_string());
            div()
                .size_full()
                .flex()
                .flex_col()
                .gap_4()
                .child(
                    div()
                        .w_full()
                        .flex()
                        .flex_col()
                        .gap_3()
                        .p_5()
                        .rounded_xl()
                        .bg(rgb(0x292a2d))
                        .child(
                            div()
                                .text_lg()
                                .font_weight(gpui::FontWeight::SEMIBOLD)
                                .text_color(rgb(0xf0eee9))
                                .child("照片保存目录"),
                        )
                        .child(
                            div()
                                .text_sm()
                                .text_color(rgb(0xc4c2be))
                                .child(save_directory),
                        )
                        .child(
                            div()
                                .text_xs()
                                .text_color(rgb(0x999a9c))
                                    .child("作为默认图库加载目录和后续导入位置；更改后立即加载，不会移动已有照片。"),
                        )
                        .child(button("选择目录…", false).on_click(
                            cx.listener(|this, _, _, cx| this.choose_photo_save_directory(cx)),
                        )),
                )
                .child(
                    div()
                        .w_full()
                        .flex()
                        .flex_col()
                        .gap_2()
                        .p_5()
                        .rounded_xl()
                        .bg(rgb(0x292a2d))
                        .child(
                            div()
                                .text_lg()
                                .font_weight(gpui::FontWeight::SEMIBOLD)
                                .text_color(rgb(0xf0eee9))
                                .child("关于"),
                        )
                        .child(
                            div()
                                .text_sm()
                                .text_color(rgb(0xc4c2be))
                                .child(format!("光屿 · 版本 {}", env!("CARGO_PKG_VERSION"))),
                        )
                        .child(
                            div()
                                .text_xs()
                                .text_color(rgb(0x999a9c))
                                .child("Rust 与 GPUI 构建的 macOS 照片管理原型"),
                        ),
                )
                .into_any_element()
        } else if self.selected_section == "日记回收站" {
            let mut trash = div().id("diary-trash-list").size_full().flex().flex_col().gap_3().overflow_y_scroll()
                .child(div().flex().items_center().justify_between()
                    .child(div().flex().flex_col().gap_1()
                        .child(div().text_2xl().font_weight(gpui::FontWeight::SEMIBOLD).text_color(rgb(0xf2f0ec)).child("日记回收站"))
                        .child(div().text_sm().text_color(rgb(0x96979a)).child(format!("{} 篇日记暂存；照片文件保留在原位置", self.diary_trash.len())))));
            if self.diary_trash.is_empty() {
                trash = trash.child(div().p_5().rounded_lg().bg(rgb(0x292a2d)).text_color(rgb(0xb7b5b1)).child("日记回收站为空。删除的日记会暂存在这里。"));
            } else {
                for entry in self.diary_trash.clone() {
                    let id = entry.id;
                    let title = if entry.title.is_empty() { "无标题日记" } else { &entry.title };
                    let snippet = entry.body.lines().next().unwrap_or("还没有写内容");
                    trash = trash.child(div().w_full().flex().items_center().gap_3().p_3().rounded_lg().border_1().border_color(rgb(0x414246)).bg(rgb(0x292a2d))
                        .child(div().flex_1().min_w(px(0.)).flex().flex_col().gap_1()
                            .child(div().text_sm().text_color(rgb(0xe5e3df)).text_ellipsis().child(title.to_string()))
                            .child(div().text_xs().text_color(rgb(0x96979a)).child(format!("{} · {} · {} 张照片", entry.category, entry.date, entry.photos.len())))
                            .child(div().text_xs().text_color(rgb(0xb7b5b1)).text_ellipsis().child(snippet.to_string())))
                        .child(button("恢复", false).id(SharedString::from(format!("restore-diary-{id}"))).on_click(cx.listener(move |this, _, _, cx| this.restore_trashed_diary(id, cx))))
                        .child(button("彻底删除", false).id(SharedString::from(format!("permanently-delete-diary-{id}"))).on_click(cx.listener(move |this, _, _, cx| this.permanently_delete_trashed_diary(id, cx)))));
                }
            }
            trash.into_any_element()
        } else if self.selected_section == "重复项" {
            self.render_duplicate_review(cx)
        } else if self.selected_section == "隔离区" {
            let files = self.source_directory.as_deref().map(list_quarantined_files).unwrap_or_default();
            let mut quarantine = div().id("quarantine-list").size_full().flex().flex_col().gap_3().overflow_y_scroll()
                .child(div().flex().items_center().justify_between()
                    .child(div().flex().flex_col().gap_1()
                        .child(div().text_2xl().font_weight(gpui::FontWeight::SEMIBOLD).text_color(rgb(0xf2f0ec)).child("隔离区"))
                        .child(div().text_sm().text_color(rgb(0x96979a)).child(format!("{} 张照片可恢复", files.len()))))
                    .child(button("恢复全部", true).on_click(cx.listener(|this, _, _, cx| this.restore_quarantined_photos(cx)))));
            if files.is_empty() {
                quarantine = quarantine.child(div().p_5().rounded_lg().bg(rgb(0x292a2d)).text_color(rgb(0xb7b5b1)).child("隔离区为空。移入隔离区的照片可在这里恢复。"));
            } else {
                for path in files {
                    let video_thumbnail = self.video_thumbnail(&path, cx);
                    let display_path = if is_supported_video(&path) {
                        path.clone()
                    } else {
                        self.photo_display_path(&path, cx)
                    };
                    let video_thumbnail = if is_supported_video(&path) { video_thumbnail } else { self.photo_thumbnail(&path, &display_path, cx) };
                    let thumbnail_failed = self.video_thumbnail_failures.contains(&path);
                    let open_path = path.clone();
                    quarantine = quarantine.child(div().w_full().flex().items_center().gap_3().p_3().rounded_lg().border_1().border_color(rgb(0x414246)).bg(rgb(0x292a2d))
                        .child(div().w(px(72.)).h(px(60.)).flex_none().rounded_md().overflow_hidden().bg(rgb(0x202124))
                            .child(media_thumbnail(&display_path, video_thumbnail, thumbnail_failed))
                            .on_mouse_down(gpui::MouseButton::Left, cx.listener(move |this, event: &gpui::MouseDownEvent, _, cx| {
                                if event.click_count >= 2 { this.open_media(open_path.clone(), cx); }
                            })))
                        .child(div().flex_1().flex().flex_col().gap_1()
                            .child(div().text_sm().text_color(rgb(0xe5e3df)).child(selectable_media_text(filename(&path), &path, "quarantine-name")))
                            .child(div().text_xs().text_color(rgb(0x96979a)).child(selectable_media_text(path.display().to_string(), &path, "quarantine-path"))))
                        .child(div().text_xs().text_color(rgb(0xb7b5b1)).child(selectable_media_text(file_size(&path), &path, "quarantine-size"))));
                }
            }
            quarantine.into_any_element()
        } else if self.selected_section == "删除区域" {
            let files = self.source_directory.as_deref().map(list_deletion_area_files).unwrap_or_default();
            let mut deletion_area = div().id("deletion-area-list").size_full().flex().flex_col().gap_3().overflow_y_scroll()
                .child(div().flex().items_center().justify_between()
                    .child(div().flex().flex_col().gap_1()
                        .child(div().text_2xl().font_weight(gpui::FontWeight::SEMIBOLD).text_color(rgb(0xf2f0ec)).child("删除区域"))
                        .child(div().text_sm().text_color(rgb(0x96979a)).child(format!("{} 张照片暂存；可恢复，永久删除需再次确认", files.len())))));
            if files.is_empty() {
                deletion_area = deletion_area.child(div().p_5().rounded_lg().bg(rgb(0x292a2d)).text_color(rgb(0xb7b5b1)).child("删除区域为空。照片移至这里后，可选择恢复或永久删除。"));
            } else {
                for path in files {
                    let restore_path = path.clone();
                    let delete_path = path.clone();
                    let confirm_delete = self.pending_permanent_delete.as_ref() == Some(&path);
                    let video_thumbnail = self.video_thumbnail(&path, cx);
                    let display_path = if is_supported_video(&path) {
                        path.clone()
                    } else {
                        self.photo_display_path(&path, cx)
                    };
                    let video_thumbnail = if is_supported_video(&path) { video_thumbnail } else { self.photo_thumbnail(&path, &display_path, cx) };
                    let thumbnail_failed = self.video_thumbnail_failures.contains(&path);
                    let open_path = path.clone();
                    deletion_area = deletion_area.child(div().w_full().flex().items_center().gap_3().p_3().rounded_lg().border_1().border_color(rgb(0x414246)).bg(rgb(0x292a2d))
                        .child(div().w(px(72.)).h(px(60.)).flex_none().rounded_md().overflow_hidden().bg(rgb(0x202124))
                            .child(media_thumbnail(&display_path, video_thumbnail, thumbnail_failed))
                            .on_mouse_down(gpui::MouseButton::Left, cx.listener(move |this, event: &gpui::MouseDownEvent, _, cx| {
                                if event.click_count >= 2 { this.open_media(open_path.clone(), cx); }
                            })))
                        .child(div().flex_1().flex().flex_col().gap_1()
                            .child(div().text_sm().text_color(rgb(0xe5e3df)).child(selectable_media_text(filename(&path), &path, "deleted-name")))
                            .child(div().text_xs().text_color(rgb(0x96979a)).child(selectable_media_text(path.display().to_string(), &path, "deleted-path"))))
                        .child(div().text_xs().text_color(rgb(0xb7b5b1)).child(selectable_media_text(file_size(&path), &path, "deleted-size")))
                        .child(button("恢复", false).on_click(cx.listener(move |this, _, _, cx| this.restore_from_deletion_area(&restore_path, cx))))
                        .child(button(if confirm_delete { "确认永久删除" } else { "永久删除" }, false).on_click(cx.listener(move |this, _, _, cx| this.permanently_delete_from_area(&delete_path, cx)))));
                }
            }
            deletion_area.into_any_element()
        } else if media.is_empty() {
            div()
                .size_full()
                .flex()
                .flex_col()
                .justify_center()
                .items_center()
                .text_color(rgb(0x999a9c))
                .child(if self.selected_section == "重复项" && !self.duplicate_scan_running && self.duplicate_groups.is_empty() {
                    "没有找到重复照片"
                } else if self.selected_section == "重复项" && self.duplicate_scan_running {
                    "正在扫描照片…"
                } else if self.photos.is_empty() {
                    "选择照片目录开始浏览"
                } else {
                    "此分类还没有媒体"
                })
                .child(
                    div().mt_2().text_sm().child(if self.selected_section == "重复项" {
                        "扫描会比对照片文件内容，完全相同的文件会归为一组。"
                    } else {
                        "支持 JPEG、PNG、GIF、WebP、TIFF、BMP、AVIF、HEIC，以及 MOV、MP4 等视频文件"
                    }),
                )
                .into_any_element()
        } else {
            match self.view_mode {
                ViewMode::Names => {
                    let indices = media.clone();
                    let name_width = self.list_name_width;
                    let date_width = self.list_date_width;
                    let size_width = self.list_size_width;
                    let kind_width = self.list_kind_width;
                    let list_width = name_width + date_width + size_width + kind_width + 48.0;
                    let mut list_timeline_targets = Vec::<(String, String, usize)>::new();
                    let mut last_month = String::new();
                    for (position, index) in indices.iter().copied().enumerate() {
                        let path = &self.photos[index];
                        let date = self.capture_dates.get(path).and_then(|date| date.as_deref())
                            .map(str::to_string).unwrap_or_else(|| modified_time(path));
                        let year = date.get(0..4).filter(|value| value.chars().all(|ch| ch.is_ascii_digit())).unwrap_or("未知").to_string();
                        let month = date.get(5..7).filter(|value| value.chars().all(|ch| ch.is_ascii_digit())).unwrap_or("未知").to_string();
                        let key = format!("{year}-{month}");
                        if key != last_month {
                            list_timeline_targets.push((year, month, position));
                            last_month = key;
                        }
                    }
                    let mut list_timeline = div().id("photo-name-timeline").w(px(76.)).h_full().flex_none().flex().flex_col().items_center().gap_2().pt_1();
                    let list_targets_for_scroll = list_timeline_targets.clone();
                    let list_timeline_app = cx.entity();
                    let mut last_year = String::new();
                    for (year, month, position) in list_timeline_targets {
                        let target_position = position;
                        let active_key = format!("{year}-{month}");
                        let active = self.active_timeline_year.as_deref() == Some(active_key.as_str());
                        let label = if year != last_year {
                            last_year = year.clone();
                            if year == "未知" { "日期未知".to_string() } else { format!("{year} 年") }
                        } else if month == "未知" { "未知月".to_string() } else { format!("{month} 月") };
                        let key = active_key;
                        list_timeline = list_timeline.child(button(label, active).w_full().on_click(cx.listener(move |this, _, _, cx| {
                            this.active_timeline_year = Some(key.clone());
                            this.timeline_scroll.scroll_to_item_strict(target_position, ScrollStrategy::Top);
                            cx.notify();
                        })));
                    }
                    let resize_handle = |column: usize, cx: &mut Context<Self>| {
                        div()
                            .id(SharedString::from(format!("list-column-resize-{column}")))
                            .w(px(6.))
                            .h_full()
                            .flex_none()
                            .cursor_col_resize()
                            .on_mouse_down(
                                gpui::MouseButton::Left,
                                cx.listener(|this, _, _, _| this.list_column_last_x = None),
                            )
                            .on_drag(
                                ListColumnResizeDrag { column },
                                |drag: &ListColumnResizeDrag, _, _, cx| {
                                    cx.new(|_| ListColumnResizeDrag {
                                        column: drag.column,
                                    })
                                },
                            )
                            .on_drag_move::<ListColumnResizeDrag>(cx.listener(
                                |this, event: &gpui::DragMoveEvent<ListColumnResizeDrag>, _, cx| {
                                    let x = event.event.position.x.to_f64() as f32;
                                    if let Some(last_x) = this.list_column_last_x {
                                        let delta = x - last_x;
                                        let width = match event.drag(cx).column {
                                            0 => &mut this.list_name_width,
                                            1 => &mut this.list_date_width,
                                            2 => &mut this.list_size_width,
                                            _ => &mut this.list_kind_width,
                                        };
                                        *width = (*width + delta).clamp(56.0, 900.0);
                                    }
                                    this.list_column_last_x = Some(x);
                                    cx.notify();
                                },
                            ))
                    };
                    div()
                        .size_full()
                        .flex()
                        .flex_col()
                        .child(
                            div()
                                .w(px(list_width))
                                .h(px(36.))
                                .flex()
                                .items_center()
                                .gap_0()
                                .px_3()
                                .rounded_md()
                                .bg(rgb(0x2d2e31))
                                .text_xs()
                                .text_color(rgb(0xaaa9a6))
                                .child(
                                    div()
                                        .w(px(name_width))
                                        .flex_none()
                                        .flex()
                                        .items_center()
                                        .gap_2()
                                        .child(div().w(px(34.)))
                                        .child("名称"),
                                )
                                .child(resize_handle(0, cx))
                                .child(div().w(px(date_width)).flex_none().child("修改日期"))
                                .child(resize_handle(1, cx))
                                .child(
                                    div()
                                        .w(px(size_width))
                                        .flex_none()
                                        .flex()
                                        .justify_end()
                                        .child("大小"),
                                )
                                .child(resize_handle(2, cx))
                                .child(div().w(px(kind_width)).flex_none().child("种类")),
                        )
                        .child(
                            div().flex().flex_1().min_h(px(0.)).gap_3()
                                .child(list_timeline)
                                .child(uniform_list(
                                "photo-name-list",
                                indices.len(),
                                cx.processor(move |this, range: std::ops::Range<usize>, _, cx| {
                                    range
                                        .map(|position| {
                                            let index = indices[position];
                                            let path = this.photos[index].clone();
                                            let drag_source_category = this.categories.iter()
                                                .any(|category| category == &this.selected_section)
                                                .then(|| this.selected_section.clone());
                                            let selected = this.selected_media == index || this.selected_paths.contains(&path);
                                            let thumbnail = this.video_thumbnail(&path, cx);
                                            let display_path = if is_supported_video(&path) {
                                                path.clone()
                                            } else {
                                                this.photo_display_path(&path, cx)
                                            };
                                            let thumbnail = if is_supported_video(&path) { thumbnail } else { this.photo_thumbnail(&path, &display_path, cx) };
                                            let drag_thumbnail = thumbnail.clone();
                                            let thumbnail_failed =
                                                this.video_thumbnail_failures.contains(&path);
                                            let hover_group =
                                                format!("photo-list-thumb-{position}");
                                            let mut small_thumbnail = div()
                                                .group(hover_group.clone())
                                                .relative()
                                                .w(px(34.))
                                                .h(px(34.))
                                                .flex_none()
                                                .rounded_sm()
                                                .overflow_hidden()
                                                .child(media_thumbnail(
                                                    &display_path,
                                                    thumbnail,
                                                    thumbnail_failed,
                                                ));
                                            if !is_supported_video(&path) {
                                                let rotate_path = path.clone();
                                                small_thumbnail = small_thumbnail.child(
                                                    div()
                                                        .id(SharedString::from(format!(
                                                            "rotate-list-{position}"
                                                        )))
                                                        .absolute()
                                                        .top_0()
                                                        .right_0()
                                                        .w(px(22.))
                                                        .h(px(22.))
                                                        .flex()
                                                        .items_center()
                                                        .justify_center()
                                                        .rounded_full()
                                                        .bg(rgba(0x17181ac8))
                                                        .text_color(rgb(0xf5f3ef))
                                                        .text_sm()
                                                        .cursor_pointer()
                                                        .opacity(0.)
                                                        .group_hover(hover_group.clone(), |style| {
                                                            style.opacity(1.)
                                                        })
                                                        .on_mouse_down(
                                                            gpui::MouseButton::Left,
                                                            cx.listener(move |this, _, _, cx| {
                                                                cx.stop_propagation();
                                                                this.selected_media = index;
                                                                this.rotate_photo(rotate_path.clone(), cx);
                                                            }),
                                                        )
                                                        .child("↻"),
                                                );
                                            }
                                            div()
                                            .id(position)
                                            .group(hover_group.clone())
                                            .w(px(list_width))
                                            .h(px(50.))
                                            .flex()
                                            .items_center()
                                            .gap_0()
                                            .px_3()
                                            .rounded_md()
                                            .bg(if selected {
                                                rgb(0x30343a)
                                            } else {
                                                rgb(0x222326)
                                            })
                                            .text_sm()
                                            .text_color(rgb(0xd8d6d2))
                                            .child(
                                                div()
                                                    .w(px(name_width))
                                                    .flex_none()
                                                    .min_w(px(0.))
                                                    .flex()
                                                    .items_center()
                                                    .gap_2()
                                                    .child(small_thumbnail)
                                                    .child(
                                                        div()
                                                            .flex_1()
                                                            .min_w(px(0.))
                                                            .overflow_hidden()
                                                            .child(selectable_media_text(filename(&path), &path, "name-list-name")),
                                                    ),
                                            )
                                            .child(
                                                div()
                                                    .w(px(date_width))
                                                    .flex_none()
                                                    .text_xs()
                                                    .text_color(rgb(0xa6a5a2))
                                                    .child(selectable_media_text(modified_time(&path), &path, "name-list-date")),
                                            )
                                            .child(resize_handle(0, cx))
                                            .child(
                                                div()
                                                    .w(px(size_width))
                                                    .flex_none()
                                                    .flex()
                                                    .justify_end()
                                                    .text_xs()
                                                    .text_color(rgb(0xa6a5a2))
                                                    .child(selectable_media_text(file_size(&path), &path, "name-list-size")),
                                            )
                                            .child(resize_handle(2, cx))
                                            .child(
                                                div()
                                                    .w(px(kind_width))
                                                    .flex_none()
                                                    .text_xs()
                                                    .text_color(rgb(0xa6a5a2))
                                                    .child(selectable_media_text(file_kind(&path), &path, "name-list-kind")),
                                            )
                                            .child(deferred(this.photo_context_menu(path.clone(), &hover_group, cx)).with_priority(200))
                                            .on_drag(MediaDrag { path: path.clone(), paths: this.drag_paths_for(&path), thumbnail: drag_thumbnail, source_category: drag_source_category.clone(), diary_source: None }, |drag, cursor_offset, _, cx| {
                                                let thumbnail = drag.thumbnail.clone();
                                                let show_removal_hint = drag.source_category.is_some();
                                                let (mut width, mut height) = thumbnail_dimensions(thumbnail.as_deref().unwrap_or(&drag.path));
                                                let stack_count = drag.paths.len().min(3);
                                                if stack_count > 1 { width = 88.; height = 68.; }
                                                let thumbnails = if stack_count > 1 {
                                                    make_drag_fan_thumbnails(&drag.paths, &drag.path, thumbnail.as_deref())
                                                } else { vec![] };
                                                let stack_width = width + stack_count.saturating_sub(1) as f32 * 12.;
                                                let hint_height = if show_removal_hint { 32. } else { 0. };
                                                let draw_offset = gpui::point(cursor_offset.x - px(stack_width / 2.), cursor_offset.y - px(height + 16. + hint_height));
                                                cx.new(move |_| MediaDragGhost { thumbnail, thumbnails, width, height, show_removal_hint, draw_offset })
                                            })
                                            .on_drag_move::<SelectionBoxDrag>(cx.listener({
                                                let marquee_path = path.clone();
                                                move |this, event: &gpui::DragMoveEvent<SelectionBoxDrag>, _, cx| {
                                                    let Some(start) = this.selection_box_start else { return; };
                                                    let end = event.event.position;
                                                    let bounds = event.bounds;
                                                    let intersects = bounds.origin.x < start.x.max(end.x)
                                                        && bounds.origin.x + bounds.size.width > start.x.min(end.x)
                                                        && bounds.origin.y < start.y.max(end.y)
                                                        && bounds.origin.y + bounds.size.height > start.y.min(end.y);
                                                    let changed = if intersects {
                                                        this.selected_media = index;
                                                        this.selected_paths.insert(marquee_path.clone())
                                                    } else { this.selected_paths.remove(&marquee_path) };
                                                    if changed { cx.notify(); }
                                                }
                                            }))
                                            .on_mouse_down(
                                                gpui::MouseButton::Right,
                                                cx.listener({
                                                    let context_path = path.clone();
                                                    move |this, event: &gpui::MouseDownEvent, _, cx| this.open_photo_context_menu(context_path.clone(), event.position, cx)
                                                }),
                                            )
                                            .on_mouse_down(
                                                gpui::MouseButton::Left,
                                                cx.listener(
                                                    move |this,
                                                          event: &gpui::MouseDownEvent,
                                                          _,
                                                          cx| {
                                                        this.last_selection_position = Some((event.position.x.to_f64() as f32, event.position.y.to_f64() as f32));
                                                        this.select_media(index, event.modifiers.shift);
                                                        cx.stop_propagation();
                                                        if event.click_count >= 2 {
                                                            this.open_media(
                                                                path.clone(),
                                                                cx,
                                                            );
                                                        }
                                                        cx.notify();
                                                    },
                                                ),
                                            )
                                        })
                                        .collect::<Vec<_>>()
                                }),
                            )
                            .on_scroll_wheel(cx.listener(move |_, _, window, _| {
                                let app = list_timeline_app.clone();
                                let targets = list_targets_for_scroll.clone();
                                window.on_next_frame(move |_, cx| {
                                    let _ = app.update(cx, |this, cx| {
                                        let scroll_top = (-this.timeline_scroll.0.borrow().base_handle.offset().y.to_f64()).max(0.0);
                                        let top_row = (scroll_top / 50.0).floor() as usize;
                                        let active = targets.iter().rev().find(|(_, _, position)| *position <= top_row)
                                            .or_else(|| targets.first())
                                            .map(|(year, month, _)| format!("{year}-{month}"));
                                        if this.active_timeline_year != active {
                                            this.active_timeline_year = active;
                                            cx.notify();
                                        }
                                    });
                                });
                            }))
                            .track_scroll(self.timeline_scroll.clone())
                            .w_full()
                            .flex_1()
                            .min_h(px(0.))),
                        )
                        .into_any_element()
                }
                ViewMode::Gallery => {
                    let selected = media
                        .iter()
                        .copied()
                        .find(|index| *index == self.selected_media)
                        .unwrap_or(media[0]);
                    let selected_path = self.photos[selected].clone();
                    let is_video = is_supported_video(&selected_path);
                    if !is_video { self.request_image_dimensions(&selected_path, cx); }
                    let selected_dimensions = if is_video { "未知".to_string() } else {
                        self.image_dimensions.get(&selected_path).and_then(|value| value.clone()).unwrap_or_else(|| "读取中…".to_string())
                    };
                    let video_duration = self
                        .video_playback
                        .as_ref()
                        .filter(|playback| playback.path == selected_path)
                        .map(|playback| {
                            format_video_time(unsafe { playback.item.duration().seconds() })
                        })
                        .unwrap_or_else(|| "未知".into());
                    self.stop_video_if_not_selected(&selected_path);
                    if self.video_playback.as_ref().is_some_and(|playback| {
                        playback.path == selected_path && (playback.playing || self.video_seeking)
                    }) {
                        self.update_video_frame();
                        if self
                            .video_playback
                            .as_ref()
                            .is_some_and(|playback| playback.playing)
                        {
                            self.video_seeking = false;
                        }
                        if self.video_controls_visible
                            && self.video_controls_last_motion.is_some_and(|last_motion| {
                                last_motion.elapsed() >= Duration::from_secs(3)
                            })
                        {
                            self.video_controls_visible = false;
                        }
                        if self
                            .video_playback
                            .as_ref()
                            .is_some_and(|playback| playback.playing || self.video_seeking)
                        {
                            window.request_animation_frame();
                        }
                    }
                    let selected_video_frame = self
                        .video_playback
                        .as_ref()
                        .filter(|playback| playback.path == selected_path)
                        .and_then(|playback| playback.frame.clone());
                    let selected_thumbnail = self.video_thumbnail(&selected_path, cx);
                    let selected_display_path = if is_supported_video(&selected_path) {
                        selected_path.clone()
                    } else {
                        self.photo_display_path(&selected_path, cx)
                    };
                    let selected_thumbnail_failed =
                        self.video_thumbnail_failures.contains(&selected_path);
                    let is_video_playing = self.video_playback.as_ref().is_some_and(|playback| {
                        playback.path == selected_path && playback.playing
                    });
                    let mut preview_canvas = div()
                        .group("gallery-preview")
                        .relative()
                        .flex_1()
                        .w_full()
                        .min_w(px(0.))
                        .min_h(px(0.))
                        .overflow_hidden()
                        .flex()
                        .justify_center()
                        .items_center()
                        .drag_over::<MediaDrag>(|style, _, _, _| style.border_2().border_color(rgb(0xd9c68f)).bg(rgb(0x302f2b)))
                        .on_drop(cx.listener(|this, drag: &MediaDrag, window, cx| {
                            let Some(diary_id) = this.selected_diary else {
                                this.notice = Some("请先选择一篇日记，再把照片拖到显示框中。".into());
                                cx.notify();
                                return;
                            };
                            let point = window.mouse_position();
                            let position = (point.x.to_f64() as f32, point.y.to_f64() as f32);
                            if this.add_media_to_diary(diary_id, &drag.paths, cx) > 0 {
                                this.trigger_diary_media_flight(&drag.path, position, cx);
                            }
                        }))
                        .drag_over::<DiaryMediaReorderDrag>(|style, _, _, _| style.border_2().border_color(rgb(0xe5b85c)).bg(rgb(0x38352c)))
                        .on_drop(cx.listener(|this, drag: &DiaryMediaReorderDrag, window, cx| {
                            let path = this.diaries.iter().find(|entry| entry.id == drag.diary_id)
                                .and_then(|entry| entry.photos.get(drag.index)).cloned();
                            if let Some(path) = path {
                                let point = window.mouse_position();
                                let position = (point.x.to_f64() as f32, point.y.to_f64() as f32);
                                this.remove_photos_from_diary(drag.diary_id, std::slice::from_ref(&path), cx);
                                this.trigger_diary_media_flight(&path, position, cx);
                            }
                        }))
                        .child(media_preview(
                            &selected_path,
                            &selected_display_path,
                            selected_thumbnail,
                            selected_thumbnail_failed,
                            selected_video_frame,
                        ));
                    if is_video {
                        let play_path = selected_path.clone();
                        let play_button_opacity = if is_video_playing { 0.0 } else { 1.0 };
                        preview_canvas = preview_canvas.child(
                            div()
                                .id("video-preview-play")
                                .absolute()
                                .top_0()
                                .bottom_0()
                                .left_0()
                                .right_0()
                                .flex()
                                .justify_center()
                                .items_center()
                                .opacity(play_button_opacity)
                                .when(is_video_playing, |element| {
                                    element.group_hover("gallery-preview", |style| style.opacity(1.))
                                })
                                .cursor_pointer()
                                .on_click(cx.listener(move |this, _, _, cx| {
                                    this.toggle_video_playback(play_path.clone(), cx)
                                }))
                                .child(
                                    div()
                                        .w(px(68.))
                                        .h(px(68.))
                                        .rounded_full()
                                        .flex()
                                        .justify_center()
                                        .items_center()
                                        .pl(px(4.))
                                        .bg(rgba(0x17181acc))
                                        .border_1()
                                        .border_color(rgba(0xffffffaa))
                                        .text_color(rgb(0xffffff))
                                        .text_2xl()
                                        .child(if is_video_playing { "❚❚" } else { "▶" }),
                                ),
                        );
                    }
                    let selected_footer = div()
                        .w_full()
                        .flex()
                        .items_center()
                        .justify_between()
                        .text_sm()
                        .text_color(rgb(0xd5d3cf))
                        .child(selectable_media_text(filename(&selected_path), &selected_path, "gallery-preview-footer-name"));
                    if is_supported_video(&selected_path) {
                        let is_playing = self.video_playback.as_ref().is_some_and(|playback| {
                            playback.path == selected_path && playback.playing
                        });
                        let (current, duration) = self
                            .video_playback
                            .as_ref()
                            .filter(|playback| playback.path == selected_path)
                            .map(|playback| unsafe {
                                (
                                    playback.player.currentTime().seconds(),
                                    playback.item.duration().seconds(),
                                )
                            })
                            .unwrap_or((0.0, 0.0));
                        let ratio = if duration.is_finite() && duration > 0.0 {
                            (current / duration).clamp(0.0, 1.0) as f32
                        } else {
                            0.0
                        };
                        let back_path = selected_path.clone();
                        let toggle_path = selected_path.clone();
                        let forward_path = selected_path.clone();
                        let control_opacity = if is_playing {
                            if self.video_controls_visible {
                                1.0
                            } else {
                                0.0
                            }
                        } else {
                            0.0
                        };
                        preview_canvas = preview_canvas.child(
                            div()
                                .id("video-hover-controls")
                                .absolute()
                                .bottom_3()
                                .left_3()
                                .right_3()
                                .flex()
                                .items_center()
                                .gap_3()
                                .px_4()
                                .py_3()
                                .rounded_lg()
                                .bg(rgb(0x25272b))
                                .text_color(rgb(0xf5f3ef))
                                .opacity(control_opacity)
                                .group_hover("gallery-preview", |style| style.opacity(1.))
                                .child(
                                    div()
                                        .id("video-seek-back")
                                        .px_1()
                                        .cursor_pointer()
                                        .on_click(cx.listener(move |this, _, _, cx| {
                                            this.seek_video(&back_path, -10.0, cx)
                                        }))
                                        .child("⏪ 10"),
                                )
                                .child(
                                    div()
                                        .id("video-play-toggle")
                                        .px_2()
                                        .cursor_pointer()
                                        .on_click(cx.listener(move |this, _, _, cx| {
                                            this.toggle_video_playback(toggle_path.clone(), cx)
                                        }))
                                        .child(if is_playing { "❚❚" } else { "▶" }),
                                )
                                .child(
                                    div()
                                        .id("video-seek-forward")
                                        .px_1()
                                        .cursor_pointer()
                                        .on_click(cx.listener(move |this, _, _, cx| {
                                            this.seek_video(&forward_path, 10.0, cx)
                                        }))
                                        .child("10 ⏩"),
                                )
                                .child(format!(
                                    "{} / {}",
                                    format_video_time(current),
                                    format_video_time(duration)
                                ))
                                .child({
                                    let seek_path = selected_path.clone();
                                    let seek_path_drag = selected_path.clone();
                                    div()
                                        .id("video-progress-track")
                                        .relative()
                                        .flex_1()
                                        .h(px(16.))
                                        .flex()
                                        .items_center()
                                        .cursor_pointer()
                                        .on_mouse_down(
                                            gpui::MouseButton::Left,
                                            cx.listener(move |_, _, _, cx| {
                                                cx.notify();
                                            }),
                                        )
                                        .child(
                                            div()
                                                .w_full()
                                                .h(px(4.))
                                                .rounded_full()
                                                .bg(rgb(0x62656b))
                                                .child(
                                                    div()
                                                        .h_full()
                                                        .w(relative(ratio))
                                                        .rounded_full()
                                                        .bg(rgb(0xf5f3ef)),
                                                ),
                                        )
                                        .on_drag(seek_path.clone(), move |path, _, _, cx| {
                                            cx.new(|_| VideoSeekDrag { path: path.clone() })
                                        })
                                        .on_drag_move::<PathBuf>(cx.listener(
                                            move |this,
                                                  event: &gpui::DragMoveEvent<PathBuf>,
                                                  _,
                                                  cx| {
                                                let width = event.bounds.size.width.to_f64();
                                                if width > 0.0 {
                                                    let x = (event.event.position.x
                                                        - event.bounds.origin.x)
                                                        .to_f64();
                                                    this.seek_video_to_ratio(
                                                        &seek_path_drag,
                                                        x / width,
                                                        cx,
                                                    );
                                                }
                                            },
                                        ))
                                }),
                        );
                    }
                    if !is_supported_video(&selected_path) {
                        let rotate_path = selected_path.clone();
                        preview_canvas = preview_canvas.child(
                            div()
                                .id("rotate-gallery-preview")
                                .absolute()
                                .top_3()
                                .right_3()
                                .p_2()
                                .rounded_md()
                                .bg(rgb(0x17181a))
                                .text_color(rgb(0xf5f3ef))
                                .opacity(0.)
                                .group_hover("gallery-preview", |style| style.opacity(1.))
                                .on_click(cx.listener(move |this, _, _, cx| {
                                    this.rotate_photo(rotate_path.clone(), cx)
                                }))
                                .child("↻"),
                        );
                    }
                    if is_supported_video(&selected_path)
                        && self
                            .video_playback
                            .as_ref()
                            .is_some_and(|playback| playback.path == selected_path)
                    {
                        let motion_path = selected_path.clone();
                        preview_canvas = preview_canvas.on_mouse_move(cx.listener(
                            move |this, _: &gpui::MouseMoveEvent, _, cx| {
                                if this
                                    .video_playback
                                    .as_ref()
                                    .is_some_and(|playback| playback.path == motion_path)
                                {
                                    this.video_controls_visible = true;
                                    this.video_controls_last_motion =
                                        Some(std::time::Instant::now());
                                    if this
                                        .video_playback
                                        .as_ref()
                                        .is_some_and(|playback| playback.playing)
                                    {
                                        let timeout_path = motion_path.clone();
                                        cx.spawn(async move |this, cx| {
                                            cx.background_executor()
                                                .timer(Duration::from_secs(3))
                                                .await;
                                            let _ = this.update(cx, |app, cx| {
                                                if app.video_playback.as_ref().is_some_and(
                                                    |playback| {
                                                        playback.path == timeout_path
                                                            && playback.playing
                                                    },
                                                ) && app.video_controls_last_motion.is_some_and(
                                                    |last| last.elapsed() >= Duration::from_secs(3),
                                                ) {
                                                    app.video_controls_visible = false;
                                                    cx.notify();
                                                }
                                            });
                                        })
                                        .detach();
                                    }
                                    cx.notify();
                                }
                            },
                        ));
                    }
                    let mut preview_timeline_targets = Vec::<(String, String, usize)>::new();
                    let mut previous_preview_month = String::new();
                    for (position, index) in media.iter().copied().enumerate() {
                        let path = &self.photos[index];
                        let date = self.capture_dates.get(path).and_then(|date| date.as_deref())
                            .map(str::to_string).unwrap_or_else(|| modified_time(path));
                        let year = date.get(0..4).filter(|value| value.chars().all(|ch| ch.is_ascii_digit())).unwrap_or("未知").to_string();
                        let month = date.get(5..7).filter(|value| value.chars().all(|ch| ch.is_ascii_digit())).unwrap_or("未知").to_string();
                        let key = format!("{year}-{month}");
                        if key != previous_preview_month {
                            preview_timeline_targets.push((year, month, position));
                            previous_preview_month = key;
                        }
                    }
                    let mut preview_timeline = div().id("gallery-preview-timeline").w(px(64.)).h_full().flex_none().flex().flex_col().items_center().gap_2().pt_1();
                    let mut previous_preview_year = String::new();
                    for (year, month, position) in preview_timeline_targets.iter().cloned() {
                        let target_position = position;
                        let key = format!("{year}-{month}");
                        let active = self.active_timeline_year.as_deref() == Some(key.as_str());
                        let label = if year != previous_preview_year {
                            previous_preview_year = year.clone();
                            if year == "未知" { "日期未知".to_string() } else { format!("{year} 年") }
                        } else if month == "未知" { "未知月".to_string() } else { format!("{month} 月") };
                        preview_timeline = preview_timeline.child(button(label, active).w_full().on_click(cx.listener(move |this, _, _, cx| {
                            this.active_timeline_year = Some(key.clone());
                            this.timeline_scroll.scroll_to_item_strict(target_position, ScrollStrategy::Top);
                            cx.notify();
                        })));
                    }
                    let preview_targets_for_scroll = preview_timeline_targets.clone();
                    let preview_timeline_app = cx.entity();
                    let indices = media.clone();
                    div()
                        .size_full()
                        .flex()
                        .gap_0()
                        .h_full()
                        .child(preview_timeline)
                        .child(
                            uniform_list(
                                "gallery-name-list",
                                indices.len(),
                                cx.processor(move |this, range: std::ops::Range<usize>, _, cx| {
                                    range
                                        .map(|position| {
                                            let index = indices[position];
                                            let path = this.photos[index].clone();
                                            let drag_source_category = this.categories.iter()
                                                .any(|category| category == &this.selected_section)
                                                .then(|| this.selected_section.clone());
                                            let active = this.selected_media == index || this.selected_paths.contains(&path);
                                            let video_thumbnail = this.video_thumbnail(&path, cx);
                                            let display_path = if is_supported_video(&path) {
                                                path.clone()
                                            } else {
                                                this.photo_display_path(&path, cx)
                                            };
                                            let video_thumbnail = if is_supported_video(&path) { video_thumbnail } else { this.photo_thumbnail(&path, &display_path, cx) };
                                            let drag_thumbnail = video_thumbnail.clone();
                                            let thumbnail_failed =
                                                this.video_thumbnail_failures.contains(&path);
                                            div()
                                                .id(position)
                                                .group(format!("gallery-item-{index}"))
                                                .w_full()
                                                .h(px(44.))
                                                .flex()
                                                .items_center()
                                                .gap_2()
                                                .px_3()
                                                .rounded_md()
                                                .bg(if active {
                                                    rgb(0x383a3d)
                                                } else {
                                                    rgb(0x222326)
                                                })
                                                .text_sm()
                                                .text_color(rgb(0xd8d6d2))
                                                .child(
                                                    div()
                                                        .w(px(28.))
                                                        .h(px(28.))
                                                        .flex_none()
                                                        .rounded_sm()
                                                        .overflow_hidden()
                                                        .child(media_thumbnail(
                                                            &display_path,
                                                            video_thumbnail,
                                                            thumbnail_failed,
                                                        )),
                                                )
                                                .child(
                                                    div()
                                                        .flex_1()
                                                        .min_w(px(0.))
                                                        .overflow_hidden()
                                                        .child(selectable_media_text(filename(&path), &path, "preview-list-name")),
                                                )
                                                .child(deferred(this.photo_context_menu(path.clone(), &format!("gallery-item-{index}"), cx)).with_priority(200))
                                                .on_drag(MediaDrag { path: path.clone(), paths: this.drag_paths_for(&path), thumbnail: drag_thumbnail, source_category: drag_source_category.clone(), diary_source: None }, |drag, cursor_offset, _, cx| {
                                                    let thumbnail = drag.thumbnail.clone();
                                                    let show_removal_hint = drag.source_category.is_some();
                                                    let (mut width, mut height) = thumbnail_dimensions(thumbnail.as_deref().unwrap_or(&drag.path));
                                                    let stack_count = drag.paths.len().min(3);
                                                    if stack_count > 1 { width = 88.; height = 68.; }
                                                    let thumbnails = if stack_count > 1 {
                                                        make_drag_fan_thumbnails(&drag.paths, &drag.path, thumbnail.as_deref())
                                                    } else { vec![] };
                                                    let stack_width = width + stack_count.saturating_sub(1) as f32 * 12.;
                                                    let hint_height = if show_removal_hint { 32. } else { 0. };
                                                    let draw_offset = gpui::point(cursor_offset.x - px(stack_width / 2.), cursor_offset.y - px(height + 16. + hint_height));
                                                    cx.new(move |_| MediaDragGhost { thumbnail, thumbnails, width, height, show_removal_hint, draw_offset })
                                                })
                                                .on_drag_move::<SelectionBoxDrag>(cx.listener({
                                                    let marquee_path = path.clone();
                                                    move |this, event: &gpui::DragMoveEvent<SelectionBoxDrag>, _, cx| {
                                                        let Some(start) = this.selection_box_start else { return; };
                                                        let end = event.event.position;
                                                        let bounds = event.bounds;
                                                        let intersects = bounds.origin.x < start.x.max(end.x)
                                                            && bounds.origin.x + bounds.size.width > start.x.min(end.x)
                                                            && bounds.origin.y < start.y.max(end.y)
                                                            && bounds.origin.y + bounds.size.height > start.y.min(end.y);
                                                        let changed = if intersects {
                                                            this.selected_media = index;
                                                            this.selected_paths.insert(marquee_path.clone())
                                                        } else { this.selected_paths.remove(&marquee_path) };
                                                        if changed { cx.notify(); }
                                                    }
                                                }))
                                                .on_mouse_down(
                                                    gpui::MouseButton::Right,
                                                    cx.listener({
                                                        let context_path = path.clone();
                                                        move |this, event: &gpui::MouseDownEvent, _, cx| this.open_photo_context_menu(context_path.clone(), event.position, cx)
                                                    }),
                                                )
                                                .on_mouse_down(
                                                    gpui::MouseButton::Left,
                                                    cx.listener(
                                                        move |this,
                                                              event: &gpui::MouseDownEvent,
                                                              _,
                                                              cx| {
                                                            this.last_selection_position = Some((event.position.x.to_f64() as f32, event.position.y.to_f64() as f32));
                                                            this.select_media(index, event.modifiers.shift);
                                                            cx.stop_propagation();
                                                            if event.click_count >= 2 {
                                                                this.open_media(
                                                                    path.clone(),
                                                                    cx,
                                                                );
                                                            }
                                                            cx.notify();
                                                        },
                                                    ),
                                                )
                                        })
                                        .collect::<Vec<_>>()
                                }),
                            )
                            .on_scroll_wheel(cx.listener(move |_, _, window, _| {
                                let app = preview_timeline_app.clone();
                                let targets = preview_targets_for_scroll.clone();
                                window.on_next_frame(move |_, cx| {
                                    let _ = app.update(cx, |this, cx| {
                                        let scroll_top = (-this.timeline_scroll.0.borrow().base_handle.offset().y.to_f64()).max(0.0);
                                        let top_row = (scroll_top / 44.0).floor() as usize;
                                        let active = targets.iter().rev().find(|(_, _, position)| *position <= top_row)
                                            .or_else(|| targets.first())
                                            .map(|(year, month, _)| format!("{year}-{month}"));
                                        if this.active_timeline_year != active {
                                            this.active_timeline_year = active;
                                            cx.notify();
                                        }
                                    });
                                });
                            }))
                            .track_scroll(self.timeline_scroll.clone())
                            .w(px((self.gallery_list_width - 64.).max(120.)))
                            .flex_none()
                            .h_full(),
                        )
                        .child(
                            div()
                                .id("gallery-splitter")
                                .w(px(10.))
                                .flex_none()
                                .h_full()
                                .flex()
                                .justify_center()
                                .items_center()
                                .cursor(gpui::CursorStyle::ResizeColumn)
                                .hover(|this| this.bg(rgb(0x383a3d)))
                                .child(div().w(px(2.)).h_full().bg(rgb(0x55575a)))
                                .on_mouse_down(
                                    gpui::MouseButton::Left,
                                    cx.listener(|this, event: &gpui::MouseDownEvent, _, _| {
                                        this.splitter_last_x =
                                            Some(event.position.x.to_f64() as f32);
                                    }),
                                )
                                .on_drag((), |_, _, _, cx| cx.new(|_| ResizeGhost))
                                .on_drag_move(cx.listener(
                                    |this, event: &gpui::DragMoveEvent<()>, _, cx| {
                                        let pointer_x = event.event.position.x.to_f64() as f32;
                                        if let Some(last_x) = this.splitter_last_x {
                                            this.gallery_list_width =
                                                (this.gallery_list_width + pointer_x - last_x)
                                                    .clamp(160., 520.);
                                        }
                                        this.splitter_last_x = Some(pointer_x);
                                        cx.notify();
                                    },
                                )),
                        )
                        .child(
                            div()
                                .flex_1()
                                .h_full()
                                .min_w(px(0.))
                                .min_h(px(0.))
                                .flex()
                                .flex_col()
                                .items_center()
                                .gap_3()
                                .bg(rgb(0x17181a))
                                .p_4()
                                .child(preview_canvas)
                                .child(selected_footer),
                        )
                        .child(
                            div()
                                .w(px(280.))
                                .flex_none()
                                .h_full()
                                .flex()
                                .flex_col()
                                .gap_4()
                                .p_4()
                                .bg(rgb(0x28292c))
                                .text_color(rgb(0xe6e4e0))
                                .child(
                                    div()
                                        .text_sm()
                                        .font_weight(gpui::FontWeight::SEMIBOLD)
                                        .child(if is_video {
                                            "视频信息"
                                        } else {
                                            "照片信息"
                                        }),
                                )
                                .child(detail_field(
                                    if is_video {
                                        "创建日期"
                                    } else {
                                        "拍摄日期"
                                    },
                                    if is_video {
                                        modified_time(&selected_path)
                                    } else {
                                        self.capture_dates
                                            .get(&selected_path)
                                            .and_then(|date| date.clone())
                                            .unwrap_or_else(|| modified_time(&selected_path))
                                    },
                                    &selected_path,
                                ))
                                .when(is_video, |panel| {
                                    panel.child(detail_field("时长", video_duration, &selected_path))
                                })
                                .child(detail_field(
                                    if is_video {
                                        "视频尺寸"
                                    } else {
                                        "照片尺寸"
                                    },
                                    if is_video {
                                        "未知".to_string()
                                    } else {
                                        selected_dimensions
                                    },
                                    &selected_path,
                                ))
                                .child(detail_field(
                                    "格式 / 大小",
                                    format!(
                                        "{} · {}",
                                        selected_path
                                            .extension()
                                            .map(|ext| ext.to_string_lossy().to_uppercase())
                                            .unwrap_or_else(|| "未知".into()),
                                        file_size(&selected_path)
                                    ),
                                    &selected_path,
                                ))
                                .child(detail_field(
                                    "位置",
                                    selected_path
                                        .parent()
                                        .map(|path| path.to_string_lossy().into_owned())
                                        .unwrap_or_else(|| "未知".into()),
                                    &selected_path,
                                ))
                                .child(
                                    div()
                                        .pt_1()
                                        .text_sm()
                                        .font_weight(gpui::FontWeight::SEMIBOLD)
                                        .child("文件名"),
                                )
                                .child(
                                    div()
                                        .text_sm()
                                        .text_color(rgb(0xbcbab6))
                                        .child(selectable_media_text(filename(&selected_path), &selected_path, "gallery-preview-info-name")),
                                ),
                        )
                        .into_any_element()
                }
                mode => {
                    let diary_reserved_width = if self.diary_column_open {
                        self.diary_column_width + 10.
                    } else {
                        0.
                    };
                    let available_width = (window.bounds().size.width.to_f64() as f32
                        - 300.
                        - diary_reserved_width)
                        .max(120.);
                    let preferred_tile = if mode == ViewMode::Small { 128. } else { 200. };
                    let columns = ((available_width + 16.) / (preferred_tile + 16.))
                        .floor()
                        .max(1.) as usize;
                    let tile =
                        ((available_width - 16. * (columns - 1) as f32) / columns as f32).max(96.);
                    let mut media_by_month = BTreeMap::<(String, String, String, String), Vec<usize>>::new();
                    for index in media.iter().copied() {
                        let path = &self.photos[index];
                        let datetime = self.capture_dates.get(path).and_then(|value| value.as_ref());
                        // While EXIF is loading, group by file timestamp temporarily. Only a
                        // completed metadata read with no capture date is truly unknown.
                        let fallback_datetime;
                        let date = if let Some(datetime) = datetime {
                            datetime.split(' ').next().unwrap_or("未知")
                        } else if !self.capture_dates.contains_key(path) {
                            fallback_datetime = modified_time(path);
                            fallback_datetime.split(' ').next().unwrap_or("未知")
                        } else {
                            "未知"
                        };
                        let year = date.get(0..4)
                            .filter(|year| year.chars().all(|character| character.is_ascii_digit()))
                            .unwrap_or("未知").to_string();
                        let month = if year == "未知" { "未知".to_string() } else {
                            date.get(5..7).filter(|month| month.chars().all(|character| character.is_ascii_digit()))
                                .map(str::to_string).unwrap_or_else(|| "未知".to_string())
                        };
                        let day = if year == "未知" { "未知".to_string() } else { date.to_string() };
                        let location = self.capture_locations.get(path).and_then(|value| value.as_deref())
                            .unwrap_or("地点未知").to_string();
                        media_by_month.entry((year, month, day, location)).or_default().push(index);
                    }
                    let mut month_rows = Vec::<(Option<(String, String, String, String, usize, usize)>, Vec<usize>)>::new();
                    for ((year, month, day, location), indices) in media_by_month.iter().rev() {
                        let photo_count = indices
                            .iter()
                            .filter(|index| is_supported_image(&self.photos[**index]))
                            .count();
                        let video_count = indices
                            .iter()
                            .filter(|index| is_supported_video(&self.photos[**index]))
                            .count();
                        for (row_number, chunk) in indices.chunks(columns).enumerate() {
                            month_rows.push((
                                (row_number == 0).then(|| (year.clone(), month.clone(), day.clone(), location.clone(), photo_count, video_count)),
                                chunk.to_vec(),
                            ));
                        }
                    }
                    self.selection_display_order = month_rows.iter().flat_map(|(_, row)| row.iter().copied()).collect();
                    let row_count = month_rows.len();
                    let mut timeline_targets = Vec::<(String, String, usize)>::new();
                    for (row, (heading, _)) in month_rows.iter().enumerate() {
                        if let Some((year, month, _, _, _, _)) = heading
                            && !timeline_targets.iter().any(|(seen_year, seen_month, _)| seen_year == year && seen_month == month)
                        {
                            timeline_targets.push((year.clone(), month.clone(), row));
                        }
                    }
                    let scroll_state = self.timeline_scroll.0.borrow();
                    let scroll_top = (-scroll_state.base_handle.offset().y.to_f64()).max(0.0);
                    let row_height = scroll_state
                        .last_item_size
                        .map(|item_size| {
                            item_size.contents.height.to_f64() / row_count.max(1) as f64
                        })
                        .filter(|height| *height > 0.0)
                        .unwrap_or(1.0);
                    let top_row = ((scroll_top / row_height).floor() as usize)
                        .min(row_count.saturating_sub(1));
                    drop(scroll_state);
                    let timeline_app = cx.entity();
                    let visible_month = timeline_targets
                        .iter()
                        .rev()
                        .find(|(_, _, row)| *row <= top_row)
                        .map(|(year, month, _)| format!("{year}-{month}"));
                    let current_active_key = self.active_timeline_year.as_ref()
                        .filter(|active| timeline_targets.iter().any(|(year, month, _)| format!("{year}-{month}") == **active))
                        .cloned()
                        .or(visible_month);
                    let mut timeline_rail = div()
                        .id("photo-year-timeline")
                        .w(px(76.))
                        .h_full()
                        .flex_none()
                        .flex()
                        .flex_col()
                        .items_center()
                        .gap_2()
                        .pt_1();
                    let mut last_timeline_year = String::new();
                    for (year, month, row) in timeline_targets.iter().cloned() {
                        let entry_key = format!("{year}-{month}");
                        let active = current_active_key.as_deref() == Some(entry_key.as_str());
                        let scroll_row = row;
                        let selected_year = entry_key.clone();
                        let animation_id = SharedString::from(format!(
                            "timeline-highlight-{year}-{}",
                            if active { "active" } else { "idle" }
                        ));
                        let year_option = div()
                            .id(SharedString::from(format!("timeline-{year}-{month}")))
                            .w_full()
                            .px_1()
                            .py_1()
                            .rounded_md()
                            .text_xs()
                            .text_center()
                            .font_weight(if active {
                                gpui::FontWeight::SEMIBOLD
                            } else {
                                gpui::FontWeight::NORMAL
                            })
                            .text_color(if active { rgb(0xc5d4ff) } else { rgb(0x9b9da2) })
                            .bg(if active { rgb(0x35436a) } else { rgb(0x222326) })
                            .hover(|style| style.bg(rgb(0x34363a)))
                            .child(if last_timeline_year != year {
                                last_timeline_year = year.clone();
                                if year == "未知" { "日期未知".to_string() } else { format!("{year} 年") }
                            } else if month == "未知" { "未知月".to_string() } else { format!("{month} 月") })
                            .on_click(cx.listener(move |this, _, _, cx| {
                                this.active_timeline_year = Some(selected_year.clone());
                                let strategy = if scroll_row + 1 == row_count {
                                    ScrollStrategy::Bottom
                                } else {
                                    ScrollStrategy::Top
                                };
                                this.timeline_scroll
                                    .scroll_to_item_strict(scroll_row, strategy);
                                cx.notify();
                            }))
                            .with_animation(
                                animation_id,
                                Animation::new(Duration::from_millis(180))
                                    .with_easing(|progress| 1.0 - (1.0 - progress).powi(3)),
                                move |element, progress| {
                                    if active {
                                        element.opacity(0.45 + 0.55 * progress)
                                    } else {
                                        element
                                    }
                                },
                            );
                        timeline_rail = timeline_rail.child(year_option);
                    }
                    let drag_targets = timeline_targets.clone();
                    timeline_rail = timeline_rail
                        .on_drag(
                            YearTimelineDrag {
                                targets: drag_targets.clone(),
                            },
                            |drag, _, _, cx| {
                                cx.new(|_| YearTimelineDrag {
                                    targets: drag.targets.clone(),
                                })
                            },
                        )
                        .on_drag_move::<YearTimelineDrag>(cx.listener(
                            move |this, event: &gpui::DragMoveEvent<YearTimelineDrag>, _, cx| {
                                let height = event.bounds.size.height.to_f64();
                                if height > 0.0 && !drag_targets.is_empty() {
                                    let y = (event.event.position.y - event.bounds.origin.y)
                                        .to_f64()
                                        .clamp(0.0, height);
                                    let index = ((y / height) * drag_targets.len() as f64)
                                        .floor()
                                        .min((drag_targets.len() - 1) as f64)
                                        as usize;
                                    let (year, month, row) = &drag_targets[index];
                                    this.active_timeline_year = Some(format!("{year}-{month}"));
                                    let strategy = if *row + 1 == row_count {
                                        ScrollStrategy::Bottom
                                    } else {
                                        ScrollStrategy::Top
                                    };
                                    this.timeline_scroll.scroll_to_item_strict(*row, strategy);
                                    cx.notify();
                                }
                            },
                        ));
                    div()
                        .size_full()
                        .flex()
                        .flex_col()
                        .child(
                            div()
                                .mb_2()
                                .flex()
                                .items_center()
                                .gap_3()
                                .child(
                                    div()
                                        .text_lg()
                                        .font_weight(gpui::FontWeight::SEMIBOLD)
                                        .text_color(rgb(0xf0eee9))
                                        .child("所有照片"),
                                )
                                .child(div().text_xs().text_color(rgb(0x96979a)).child(format!(
                                        "{} 张照片 · {} 个视频",
                                        media
                                            .iter()
                                            .filter(|i| is_supported_image(&self.photos[**i]))
                                            .count(),
                                        media
                                            .iter()
                                            .filter(|i| is_supported_video(&self.photos[**i]))
                                            .count()
                                    )))
                                .child(div().flex_1()),
                        )
                        .child(
                            div()
                                .flex_1()
                                .min_h(px(0.))
                                .flex()
                                .gap_2()
                                .child(timeline_rail)
                                .child(
                                    uniform_list(
                                        if mode == ViewMode::Small {
                                            "photo-small-grid"
                                        } else {
                                            "photo-large-grid"
                                        },
                                        row_count,
                                        cx.processor(
                                            move |this, rows: std::ops::Range<usize>, _, cx| {
                                                rows.map(|row_index| {
                                        let (month_header, row_indices) = &month_rows[row_index];
                                        let heading =
                                            if let Some((year, month, day, location, photos, videos)) = month_header {
                                                div()
                                                    .h(px(42.))
                                                    .flex()
                                                    .flex_col()
                                                    .items_start()
                                                    .justify_start()
                                                    .gap_0()
                                                    .child(
                                                        div()
                                                            .text_sm()
                                                            .font_weight(gpui::FontWeight::SEMIBOLD)
                                                            .text_color(rgb(0xf0eee9))
                                                            .child(if day == "未知" {
                                                                "日期未知".to_string()
                                                            } else {
                                                                format!("{location} · {day}")
                                                            }),
                                                    )
                                                    .child(
                                                        div()
                                                            .text_xs()
                                                            .text_color(rgb(0x96979a))
                                                            .child(if day == "未知" {
                                                                format!("{location} · {photos} 张照片 · {videos} 个视频")
                                                            } else {
                                                                format!("{year} 年 {month} 月 · {photos} 张照片 · {videos} 个视频")
                                                            }),
                                                    )
                                            } else {
                                                div().h(px(42.))
                                            };
                                        // Keep enough vertical room for the thumbnail and both
                                        // caption lines. The old row estimate was shorter than
                                        // the rendered card, so captions could spill into the
                                        // next date heading in the virtualized list.
                                        let mut media_row =
                                            div().flex().gap_4().h(px(tile * 0.78 + 64.));
                                        for index in row_indices.iter().copied() {
                                            let position = index;
                                            let path = this.photos[index].clone();
                                            let selected = this.selected_media == index;
                                            let drag_source_category = this.categories.iter()
                                                .any(|category| category == &this.selected_section)
                                                .then(|| this.selected_section.clone());
                                            let viewer_path = path.clone();
                                            let video_thumbnail = this.video_thumbnail(&path, cx);
                                            let display_path = if is_supported_video(&path) {
                                                path.clone()
                                            } else {
                                                this.photo_display_path(&path, cx)
                                            };
                                            let video_thumbnail = if is_supported_video(&path) { video_thumbnail } else { this.photo_thumbnail(&path, &display_path, cx) };
                                            let drag_thumbnail = video_thumbnail.clone();
                                            let video_thumbnail_failed =
                                                this.video_thumbnail_failures.contains(&path);
                                            let hover_group = format!("photo-thumbnail-{position}");
                                            let mut thumbnail_card = div()
                                                .id(SharedString::from(path.display().to_string()))
                                                .group(hover_group.clone())
                                                .relative()
                                                .w(px(tile))
                                                .h(px(tile * 0.78))
                                                .rounded_lg()
                                                .border_2()
                                                .border_color(if this.selected_paths.contains(&path) {
                                                    rgb(0xf2c36b)
                                                } else if selected {
                                                    rgb(0x88a9ff)
                                                } else {
                                                    rgb(0x333538)
                                                })
                                                .child(div()
                                                    .size_full()
                                                    .rounded_lg()
                                                    .overflow_hidden()
                                                    .child(media_thumbnail(
                                                        &display_path,
                                                        video_thumbnail,
                                                        video_thumbnail_failed,
                                                    )));
                                            thumbnail_card = thumbnail_card.on_drag(MediaDrag { path: path.clone(), paths: this.drag_paths_for(&path), thumbnail: drag_thumbnail, source_category: drag_source_category, diary_source: None }, |drag, cursor_offset, _, cx| {
                                                let thumbnail = drag.thumbnail.clone();
                                                let show_removal_hint = drag.source_category.is_some();
                                                let (mut width, mut height) = thumbnail_dimensions(thumbnail.as_deref().unwrap_or(&drag.path));
                                                let stack_count = drag.paths.len().min(3);
                                                if stack_count > 1 { width = 88.; height = 68.; }
                                                let thumbnails = if stack_count > 1 {
                                                    make_drag_fan_thumbnails(&drag.paths, &drag.path, thumbnail.as_deref())
                                                } else { vec![] };
                                                let stack_width = width + stack_count.saturating_sub(1) as f32 * 12.;
                                                let hint_height = if show_removal_hint { 32. } else { 0. };
                                                let draw_offset = gpui::point(cursor_offset.x - px(stack_width / 2.), cursor_offset.y - px(height + 16. + hint_height));
                                                cx.new(move |_| MediaDragGhost { thumbnail, thumbnails, width, height, show_removal_hint, draw_offset })
                                            });
                                            let marquee_path = path.clone();
                                            thumbnail_card = thumbnail_card.on_drag_move::<SelectionBoxDrag>(cx.listener(move |this, event: &gpui::DragMoveEvent<SelectionBoxDrag>, _, cx| {
                                                let Some(start) = this.selection_box_start else { return; };
                                                let end = event.event.position;
                                                let bounds = event.bounds;
                                                let left = start.x.min(end.x);
                                                let top = start.y.min(end.y);
                                                let right = start.x.max(end.x);
                                                let bottom = start.y.max(end.y);
                                                let card_right = bounds.origin.x + bounds.size.width;
                                                let card_bottom = bounds.origin.y + bounds.size.height;
                                                let intersects = bounds.origin.x < right && card_right > left && bounds.origin.y < bottom && card_bottom > top;
                                                let changed = if intersects {
                                                    this.selected_media = index;
                                                    this.selected_paths.insert(marquee_path.clone())
                                                } else { this.selected_paths.remove(&marquee_path) };
                                                if changed { cx.notify(); }
                                            }));
                                            if is_supported_video(&path) {
                                                thumbnail_card = thumbnail_card.child(
                                                    div()
                                                        .absolute()
                                                        .top_0()
                                                        .left_0()
                                                        .size_full()
                                                        .flex()
                                                        .justify_center()
                                                        .items_center()
                                                        .text_lg()
                                                        .text_color(rgb(0xf5f3ef))
                                                        .child("▶"),
                                                );
                                            }
                                            if !is_supported_video(&path)
                                                && let Some(live_movie) = live_photo_movie(&path)
                                            {
                                                thumbnail_card = thumbnail_card.child(
                                                    div()
                                                        .id(SharedString::from(format!("live-photo-{position}")))
                                                        .absolute().top_2().left_2()
                                                        .px_2().py_1().rounded_full()
                                                        .bg(rgba(0x17181ad0))
                                                        .text_xs().text_color(rgb(0xffffff))
                                                        .cursor_pointer()
                                                        .on_mouse_down(gpui::MouseButton::Left, cx.listener(move |this, _, _, cx| {
                                                            cx.stop_propagation();
                                                            this.open_media(live_movie.clone(), cx);
                                                        }))
                                                        .child("LIVE ▶"),
                                                );
                                            }
                                            if !is_supported_video(&path) {
                                                let rotate_path = path.clone();
                                                thumbnail_card = thumbnail_card.child(
                                                    div()
                                                        .id(SharedString::from(format!(
                                                            "rotate-grid-{position}"
                                                        )))
                                                        .absolute()
                                                        .top_2()
                                                        .right_2()
                                                        .w(px(28.))
                                                        .h(px(28.))
                                                        .flex()
                                                        .items_center()
                                                        .justify_center()
                                                        .rounded_full()
                                                        .bg(rgba(0x17181ac8))
                                                        .text_color(rgb(0xf5f3ef))
                                                        .text_base()
                                                        .cursor_pointer()
                                                        .opacity(0.)
                                                        .group_hover(hover_group.clone(), |style| {
                                                            style.opacity(1.)
                                                        })
                                                        .on_mouse_down(
                                                            gpui::MouseButton::Left,
                                                            cx.listener(move |this, _, _, cx| {
                                                                cx.stop_propagation();
                                                                this.selected_media = index;
                                                                this.rotate_photo(rotate_path.clone(), cx);
                                                            }),
                                                        )
                                                        .child("↻"),
                                                );
                                            }
                                            thumbnail_card = thumbnail_card.on_mouse_down(
                                        gpui::MouseButton::Left,
                                        cx.listener(
                                            move |this, event: &gpui::MouseDownEvent, _, cx| {
                                                this.last_selection_position = Some((event.position.x.to_f64() as f32, event.position.y.to_f64() as f32));
                                                this.select_media(index, event.modifiers.shift);
                                                cx.stop_propagation();
                                                if event.click_count >= 2 {
                                                    this.open_media(viewer_path.clone(), cx);
                                                }
                                                cx.notify();
                                            },
                                        ),
                                    );
                                            let context_path = path.clone();
                                            thumbnail_card = thumbnail_card.on_mouse_down(
                                                gpui::MouseButton::Right,
                                                cx.listener(move |this, event: &gpui::MouseDownEvent, _, cx| {
                                                    this.open_photo_context_menu(context_path.clone(), event.position, cx);
                                                }),
                                            );
                                            thumbnail_card = thumbnail_card.child(deferred(
                                                this.photo_context_menu(path.clone(), &hover_group, cx),
                                            ).with_priority(200));
                                            media_row = media_row.child(
                                                div()
                                                    .w(px(tile))
                                                    .flex_none()
                                                    .flex()
                                                    .flex_col()
                                                    .gap_2()
                                                    .child(thumbnail_card)
                                                    .child(
                                                        div()
                                                            .w_full()
                                                            .flex()
                                                            .flex_col()
                                                            .gap_1()
                                                            .min_w(px(0.))
                                                            .child(
                                                                div()
                                                                    .w_full()
                                                                    .text_xs()
                                                                    .text_color(rgb(0xc9c7c3))
                                                                    .child(selectable_media_text(filename(&path), &path, "grid-name")),
                                                            )
                                                            .child(
                                                                div()
                                                                    .w_full()
                                                                    .text_xs()
                                                                    .text_color(rgb(0x898b90))
                                                                    .child(selectable_media_text(format!(
                                                                        "{} · {}",
                                                                        file_kind(&path),
                                                                        file_size(&path)
                                                                    ), &path, "grid-kind-size")),
                                                            ),
                                                    ),
                                            );
                                        }
                                        div()
                                            .id(row_index)
                                            .flex()
                                            .flex_col()
                                            .h(px(tile * 0.78 + 106.))
                                            .child(heading)
                                            .child(media_row)
                                    })
                                    .collect::<Vec<_>>()
                                            },
                                        ),
                                    )
                                    .on_scroll_wheel(cx.listener(move |_, _, window, _| {
                                        let app = timeline_app.clone();
                                        let targets = timeline_targets.clone();
                                        let row_count = row_count;
                                        window.on_next_frame(move |_, cx| {
                                            let _ = app.update(cx, |this, cx| {
                                                let state = this.timeline_scroll.0.borrow();
                                                let scroll_top =
                                                    (-state.base_handle.offset().y.to_f64())
                                                        .max(0.0);
                                                let row_height = state
                                                    .last_item_size
                                                    .map(|item_size| {
                                                        item_size.contents.height.to_f64()
                                                            / row_count.max(1) as f64
                                                    })
                                                    .filter(|height| *height > 0.0)
                                                    .unwrap_or(1.0);
                                                let top_row = ((scroll_top / row_height).floor()
                                                    as usize)
                                                    .min(row_count.saturating_sub(1));
                                                drop(state);
                                                let visible_month = targets
                                                    .iter()
                                                    .rev()
                                                    .find(|(_, _, row)| *row <= top_row)
                                                    .map(|(year, month, _)| format!("{year}-{month}"));
                                                if this.active_timeline_year != visible_month {
                                                    this.active_timeline_year = visible_month;
                                                    cx.notify();
                                                }
                                            });
                                        });
                                    }))
                                    .size_full()
                                    .track_scroll(self.timeline_scroll.clone()),
                                ),
                        )
                        .into_any_element()
                }
            }
        };

        let custom_media_section = matches!(self.selected_section.as_str(), "重复项" | "隔离区" | "删除区域");
        let header = if custom_media_section { div().size_0().into_any_element() } else { header.into_any_element() };
        let toolbar = if custom_media_section { div().size_0().into_any_element() } else { toolbar.into_any_element() };
        let mut media_scroll = div()
            .id("media-scroll")
            .relative()
            .flex_1()
            .overflow_hidden()
            .on_mouse_down(
                gpui::MouseButton::Left,
                cx.listener(|this, event: &gpui::MouseDownEvent, _, cx| {
                    this.selection_box_start = Some(event.position);
                    this.selection_box_rect = None;
                    this.selected_paths.clear();
                    this.selection_anchor = None;
                    cx.notify();
                }),
            )
            .on_mouse_up(gpui::MouseButton::Left, cx.listener(|this, _, _, cx| {
                this.selection_box_start = None;
                this.selection_box_rect = None;
                cx.notify();
            }))
            .on_drag(SelectionBoxDrag, |_, _, _, cx| cx.new(|_| SelectionBoxDrag))
            .on_drag_move::<SelectionBoxDrag>(cx.listener(|this, event: &gpui::DragMoveEvent<SelectionBoxDrag>, _, cx| {
                let Some(start) = this.selection_box_start else { return; };
                let end = event.event.position;
                let left = (start.x.min(end.x) - event.bounds.origin.x).to_f64() as f32;
                let top = (start.y.min(end.y) - event.bounds.origin.y).to_f64() as f32;
                let width = (start.x - end.x).abs().to_f64() as f32;
                let height = (start.y - end.y).abs().to_f64() as f32;
                this.last_selection_position = Some((end.x.to_f64() as f32, end.y.to_f64() as f32));
                this.selection_box_rect = Some((left, top, width, height));
                cx.notify();
            }))
            .child(content);
        if let Some((left, top, width, height)) = self.selection_box_rect {
            media_scroll = media_scroll.child(
                div().id("selection-marquee").absolute().left(px(left)).top(px(top))
                    .w(px(width)).h(px(height)).border_1().border_color(rgb(0x88a9ff))
                    .bg(rgba(0x6a8fe52a)),
            );
        }
        media_scroll = media_scroll.drag_over::<DiaryMediaReorderDrag>(|style, _, _, _| style.bg(rgb(0x302f2b)))
            .on_drop(cx.listener(|this, drag: &DiaryMediaReorderDrag, window, cx| {
                let path = this.diaries.iter().find(|entry| entry.id == drag.diary_id)
                    .and_then(|entry| entry.photos.get(drag.index)).cloned();
                if let Some(path) = path {
                    let position = window.mouse_position();
                    let position = (position.x.to_f64() as f32, position.y.to_f64() as f32);
                    if let Some(thumbnail) = this.prepare_delete_flight_thumbnail(&path) {
                        let bounds = window.bounds();
                        let photo_left = 220.0;
                        let photo_right = (bounds.size.width.to_f64() as f32 - this.diary_column_width - 10.0).max(photo_left + 80.0);
                        let destination = ((photo_left + photo_right) / 2.0, bounds.size.height.to_f64() as f32 * 0.5);
                        this.trigger_photo_flight_to(thumbnail, position, destination, cx);
                    }
                    this.remove_photos_from_diary(drag.diary_id, std::slice::from_ref(&path), cx);
                    cx.stop_propagation();
                }
            }))
            .on_drop(cx.listener(|this, drag: &MediaDrag, window, cx| {
            if let Some(diary_id) = drag.diary_source {
                let position = window.mouse_position();
                let position = (position.x.to_f64() as f32, position.y.to_f64() as f32);
                if let Some(thumbnail) = this.prepare_delete_flight_thumbnail(&drag.path) {
                    let bounds = window.bounds();
                    let photo_left = 220.0;
                    let photo_right = (bounds.size.width.to_f64() as f32 - this.diary_column_width - 10.0).max(photo_left + 80.0);
                    let destination = ((photo_left + photo_right) / 2.0, bounds.size.height.to_f64() as f32 * 0.5);
                    this.trigger_photo_flight_to(thumbnail, position, destination, cx);
                }
                this.remove_photos_from_diary(diary_id, &drag.paths, cx);
                cx.stop_propagation();
            }
        }));

        let mut root = div()
            .size_full()
            .relative()
            .flex()
            .bg(rgb(0x222326))
            .child(sidebar)
            .child(
                div()
                    .flex_1()
                    .h_full()
                    .min_w(px(0.))
                    .flex()
                    .flex_col()
                    .p_5()
                    .child(header)
                    .child(toolbar)
                    .child(media_scroll)
                    .on_drop(cx.listener(|this, drag: &MediaDrag, window, cx| {
                        if let Some(category) = drag.source_category.as_deref() {
                            this.remove_paths_from_category(
                                category,
                                &drag.paths,
                                { let p = window.mouse_position(); (p.x.to_f64() as f32, p.y.to_f64() as f32) },
                                cx,
                            );
                        }
                    })),
            );

        if self.diary_column_open {
            root = root.child(
                div().id("diary-column-splitter").w(px(10.)).flex_none().h_full().flex().justify_center().items_center()
                    .cursor(gpui::CursorStyle::ResizeColumn).hover(|style| style.bg(rgb(0x383a3d)))
                    .child(div().w(px(2.)).h_full().bg(rgb(0x55575a)))
                    .on_mouse_down(gpui::MouseButton::Left, cx.listener(|this, event: &gpui::MouseDownEvent, _, _| {
                        this.diary_splitter_last_x = Some(event.position.x.to_f64() as f32);
                    }))
                    .on_drag((), |_, _, _, cx| cx.new(|_| ResizeGhost))
                    .on_drag_move(cx.listener(|this, event: &gpui::DragMoveEvent<()>, _, cx| {
                        let pointer_x = event.event.position.x.to_f64() as f32;
                        if let Some(last_x) = this.diary_splitter_last_x {
                            this.diary_column_width = (this.diary_column_width - (pointer_x - last_x)).clamp(280., 760.);
                        }
                        this.diary_splitter_last_x = Some(pointer_x);
                        cx.notify();
                    })),
            ).child(self.render_diary_column(window.bounds().size.height.to_f64() as f32, cx));
        }
        if let Some(photo) = self.diary_zoom_photo.clone() {
            let display_path = self.photo_display_path(&photo, cx);
            root = root.child(
                div().id("diary-photo-zoom-overlay").absolute().left(px(0.)).top(px(0.)).right(px(0.)).bottom(px(0.))
                    .flex().items_center().justify_center().p_6().bg(rgba(0x08090beF))
                    .on_click(cx.listener(|this, _, _, cx| { this.diary_zoom_photo = None; cx.notify(); }))
                    .child(div().id("diary-photo-zoom-image")
                        .w(px(window.bounds().size.width.to_f64() as f32 - 48.))
                        .h(px(window.bounds().size.height.to_f64() as f32 - 48.))
                        .flex().items_center().justify_center()
                        .on_click(|_, _, cx| cx.stop_propagation())
                        .child(img(display_path).size_full().object_fit(ObjectFit::Contain)
                            .with_loading(|| image_loading()).with_fallback(|| image_error())))
                    .child(button("×", false).absolute().top(px(18.)).right(px(18.))
                        .on_click(cx.listener(|this, _, _, cx| { this.diary_zoom_photo = None; cx.notify(); }))),
            );
        }
        root = root.on_key_down(cx.listener(|this, event: &gpui::KeyDownEvent, _, cx| {
            let key = event.keystroke.key.as_str();
            if key == "escape" && this.diary_zoom_photo.take().is_some() { cx.notify(); return; }
            if this.view_mode == ViewMode::Gallery && !event.keystroke.modifiers.modified() {
                let visible = this.visible_media();
                if let Some(position) = visible.iter().position(|index| *index == this.selected_media) {
                    let target = match key {
                        "up" | "left" => position.checked_sub(1),
                        "down" | "right" => (position + 1 < visible.len()).then_some(position + 1),
                        _ => None,
                    };
                    if let Some(target) = target {
                        this.select_media(visible[target], false);
                        cx.stop_propagation();
                        cx.notify();
                        return;
                    }
                }
            }
            if key == "backspace" || key == "delete" {
                if !this.selected_paths.is_empty() { this.delete_selected_photos(cx); }
            } else if key.eq_ignore_ascii_case("c") && event.keystroke.modifiers.platform {
                this.copy_selected_photos();
                cx.notify();
            }
        }));
        if let Some((x, y, effect_id)) = self.category_removal_effect {
            let animation_id = SharedString::from(format!("category-removal-{effect_id}"));
            root = root.child(
                div()
                    .absolute()
                    .top(px(y - 24.))
                    .left(px(x - 24.))
                    .w(px(48.))
                    .h(px(48.))
                    .flex()
                    .justify_center()
                    .items_center()
                    .child(
                        div()
                            .w(px(8.))
                            .h(px(8.))
                            .rounded_full()
                            .border_2()
                            .border_color(rgb(0xffca69))
                            .with_animation(
                                SharedString::from(format!("{animation_id}-burst")),
                                Animation::new(Duration::from_millis(650))
                                    .with_easing(|progress| 1.0 - (1.0 - progress).powi(3)),
                                |element, progress| {
                                    let diameter = 8. + progress * 38.;
                                    element.w(px(diameter)).h(px(diameter)).opacity(1.0 - progress)
                                },
                            ),
                    )
                    .child(
                        div()
                            .text_2xl()
                            .text_color(rgb(0xffffd1))
                            .child("✹")
                            .with_animation(
                                SharedString::from(format!("{animation_id}-spark")),
                                Animation::new(Duration::from_millis(500))
                                    .with_easing(|progress| 1.0 - (1.0 - progress).powi(3)),
                                |element, progress| element.opacity(1.0 - progress),
                            ),
                    ),
            );
        }
        if let Some((thumbnail, start_x, start_y, target_x, target_y, flight_id)) = self.photo_delete_flight.clone() {
            // Deletions fly to the sidebar quarantine area; diary photos fly back into the gallery.
            let (end_x, end_y) = if target_x.is_finite() && target_y.is_finite() {
                (target_x, target_y)
            } else {
                (110.0, (window.bounds().size.height.to_f64() as f32 - 190.0).clamp(400.0, 570.0))
            };
            let animation_id = SharedString::from(format!("photo-delete-flight-{flight_id}"));
            root = root.child(
                img(thumbnail)
                    .absolute()
                    .left(px(start_x - 44.))
                    .top(px(start_y - 34.))
                    .w(px(88.))
                    .h(px(68.))
                    .rounded_md()
                    .border_1()
                    .border_color(rgb(0xf0c56f))
                    .object_fit(ObjectFit::Cover)
                    .with_animation(
                        animation_id,
                        Animation::new(Duration::from_millis(820))
                            .with_easing(|progress| 1.0 - (1.0 - progress).powi(3)),
                        move |element, progress| {
                            element
                                .left(px(start_x - 44. + (end_x - start_x) * progress))
                                .top(px(start_y - 34. + (end_y - start_y) * progress))
                                .w(px(88. - 66. * progress))
                                .h(px(68. - 50. * progress))
                                .opacity(1.0 - progress * 0.2)
                        },
                    ),
            );
        }
        root
    }
}

fn thumbnail_dimensions(path: &Path) -> (f32, f32) {
    let dimensions = Command::new("/usr/bin/sips")
        .args(["-g", "pixelWidth", "-g", "pixelHeight"])
        .arg(path)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).into_owned())
        .and_then(|text| {
            let mut width = None;
            let mut height = None;
            for line in text.lines() {
                if let Some(value) = line.split(':').nth(1).and_then(|value| value.trim().parse::<f32>().ok()) {
                    if line.contains("pixelWidth") { width = Some(value); }
                    if line.contains("pixelHeight") { height = Some(value); }
                }
            }
            Some((width?, height?))
        })
        .filter(|(width, height)| *width > 0. && *height > 0.)
        .unwrap_or((144., 112.));
    let scale = (180. / dimensions.0).min(140. / dimensions.1).min(1.);
    ((dimensions.0 * scale).max(1.), (dimensions.1 * scale).max(1.))
}

fn make_drag_fan_thumbnails(paths: &[PathBuf], primary_path: &Path, primary_thumbnail: Option<&Path>) -> Vec<PathBuf> {
    let sources: Vec<PathBuf> = paths.iter().take(3).filter_map(|path| {
        if path == primary_path { return primary_thumbnail.map(Path::to_path_buf); }
        let cached = if is_supported_video(path) { video_thumbnail_cache_path(path) } else { photo_thumbnail_cache_path(path) };
        cached.filter(|thumbnail| thumbnail.is_file())
    }).collect();
    let count = sources.len();
    let center = (count.saturating_sub(1) as f32) / 2.0;
    sources.iter().enumerate().map(|(index, source)| {
        let angle = (index as f32 - center) * 12.0;
        let mut key = Sha256::new();
        key.update(source.as_os_str().to_string_lossy().as_bytes());
        key.update(angle.to_le_bytes());
        let digest = format!("{:x}", key.finalize());
        let target = env::temp_dir().join("guangyu-drag-fan-v3").join(format!("{digest}.png"));
        if target.is_file() { return target; }
        if let Some(parent) = target.parent() { let _ = fs::create_dir_all(parent); }
        if render_rotated_drag_card(source, angle, &target).is_ok() { target } else { source.to_path_buf() }
    }).collect()
}

fn render_rotated_drag_card(source: &Path, degrees: f32, destination: &Path) -> Result<(), Box<dyn std::error::Error>> {
    use image::{Rgba, RgbaImage, imageops::{FilterType, resize}};

    let image = image::open(source)?;
    // Render at 2x and downsample in GPUI so both the rotated edges and image details stay smooth.
    let scaled = resize(&image, 156, 112, FilterType::Lanczos3);
    let mut card = RgbaImage::from_pixel(156, 112, Rgba([0, 0, 0, 0]));
    for y in 0..112 {
        for x in 0..156 {
            card.put_pixel(x, y, scaled.get_pixel(x, y).to_owned());
        }
    }

    let radians = degrees.to_radians();
    let (sin, cos) = radians.sin_cos();
    let width = card.width() as f32;
    let height = card.height() as f32;
    let out_width = (width * cos.abs() + height * sin.abs()).ceil() as u32;
    let out_height = (height * cos.abs() + width * sin.abs()).ceil() as u32;
    let mut rotated = RgbaImage::from_pixel(out_width, out_height, Rgba([0, 0, 0, 0]));
    for y in 0..out_height {
        for x in 0..out_width {
            let dx = x as f32 + 0.5 - out_width as f32 / 2.0;
            let dy = y as f32 + 0.5 - out_height as f32 / 2.0;
            let source_x = cos * dx + sin * dy + width / 2.0 - 0.5;
            let source_y = -sin * dx + cos * dy + height / 2.0 - 0.5;
            if source_x >= 0.0 && source_y >= 0.0 && source_x < width - 1.0 && source_y < height - 1.0 {
                let x0 = source_x.floor() as u32;
                let y0 = source_y.floor() as u32;
                let tx = source_x - x0 as f32;
                let ty = source_y - y0 as f32;
                let p00 = card.get_pixel(x0, y0).0;
                let p10 = card.get_pixel(x0 + 1, y0).0;
                let p01 = card.get_pixel(x0, y0 + 1).0;
                let p11 = card.get_pixel(x0 + 1, y0 + 1).0;
                let mut channels = [0; 4];
                for channel in 0..4 {
                    let top = p00[channel] as f32 * (1.0 - tx) + p10[channel] as f32 * tx;
                    let bottom = p01[channel] as f32 * (1.0 - tx) + p11[channel] as f32 * tx;
                    channels[channel] = (top * (1.0 - ty) + bottom * ty).round().clamp(0.0, 255.0) as u8;
                }
                rotated.put_pixel(x, y, Rgba(channels));
            }
        }
    }
    rotated.save(destination)?;
    Ok(())
}

fn image_error() -> gpui::AnyElement {
    div()
        .size_full()
        .flex()
        .justify_center()
        .items_center()
        .bg(rgb(0x383a3d))
        .text_color(rgb(0xc9c7c3))
        .child("此格式暂时无法预览")
        .into_any_element()
}

fn image_loading() -> gpui::AnyElement {
    div()
        .size_full()
        .flex()
        .justify_center()
        .items_center()
        .bg(rgb(0x2b2d30))
        .text_color(rgb(0x8c8e91))
        .child("正在加载照片…")
        .into_any_element()
}

fn main() {
    Application::new().run(|cx: &mut App| {
        cx.bind_keys([
            gpui::KeyBinding::new("backspace", DiaryBackspace, Some("DiaryTextField")),
            gpui::KeyBinding::new("delete", DiaryDelete, Some("DiaryTextField")),
            gpui::KeyBinding::new("left", DiaryLeft, Some("DiaryTextField")),
            gpui::KeyBinding::new("right", DiaryRight, Some("DiaryTextField")),
            gpui::KeyBinding::new("shift-left", DiarySelectLeft, Some("DiaryTextField")),
            gpui::KeyBinding::new("shift-right", DiarySelectRight, Some("DiaryTextField")),
            gpui::KeyBinding::new("cmd-a", DiarySelectAll, Some("DiaryTextField")),
            gpui::KeyBinding::new("cmd-v", DiaryPaste, Some("DiaryTextField")),
            gpui::KeyBinding::new("cmd-c", DiaryCopy, Some("DiaryTextField")),
            gpui::KeyBinding::new("cmd-x", DiaryCut, Some("DiaryTextField")),
        ]);
        let bounds = Bounds::centered(None, size(px(1180.), px(760.)), cx);
        cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                ..Default::default()
            },
            |_, cx| {
                let photo_save_directory = load_photo_directory();
                let (categories, category_items) = load_category_index();
                let diaries = load_diaries();
                let diary_trash = load_diary_trash();
                let next_diary_id = diaries.iter().map(|entry| entry.id).max().unwrap_or(0).saturating_add(1);
                cx.new(move |_| PhotoApp {
                    selected_section: "图库".into(),
                    diary_column_open: false,
                    diaries,
                    diary_trash,
                    diary_filter: "全部".into(),
                    selected_diary: None,
                    diary_editing: false,
                    diary_title_draft: String::new(),
                    diary_body_draft: String::new(),
                    diary_category_draft: "日常".into(),
                    diary_scroll: gpui::ScrollHandle::new(),
                    diary_title_edit: None,
                    diary_body_edit: None,
                    diary_photo_index: 0,
                    diary_zoom_photo: None,
                    diary_swipe_start: None,
                    diary_swipe_consumed: false,
                    diary_horizontal_scroll: 0.,
                    diary_horizontal_scroll_handled: false,
                    next_diary_id,
                    view_mode: ViewMode::Large,
                    categories,
                    category_items,
                    category_removal_effect: None,
                    category_removal_effect_id: 0,
                    photo_delete_flight: None,
                    photo_delete_flight_id: 0,
                    last_selection_position: None,
                    selected_media: 0,
                    timeline_scroll: UniformListScrollHandle::new(),
                    active_timeline_year: None,
                    notice: None,
                    photos: Vec::new(),
                    heic_previews: HashMap::new(),
                    heic_preview_requests: HashSet::new(),
                    heic_preview_failures: HashSet::new(),
                    photo_thumbnails: HashMap::new(),
                    photo_thumbnail_requests: HashSet::new(),
                    photo_thumbnail_failures: HashSet::new(),
                    duplicate_groups: Vec::new(),
                    duplicate_scan_running: false,
                    duplicate_scan_completed: false,
                    duplicate_selected: HashSet::new(),
                    duplicate_keep_paths: HashMap::new(),
                    selected_paths: HashSet::new(),
                    selection_anchor: None,
                    selection_display_order: Vec::new(),
                    selection_box_start: None,
                    selection_box_rect: None,
                    duplicate_scan_recursive: true,
                    duplicate_scope_menu_open: false,
                    capture_dates: HashMap::new(),
                    capture_date_requests: HashSet::new(),
                    capture_locations: HashMap::new(),
                    image_dimensions: HashMap::new(),
                    image_sizes: HashMap::new(),
                    diary_capture_info: HashMap::new(),
                    image_dimensions_requests: HashSet::new(),
                    source_directory: photo_save_directory.clone(),
                    sort_mode: SortMode::CaptureDate,
                    sort_menu_open: false,
                    photo_context_menu: None,
                    photo_context_menu_hovered: false,
                    pending_permanent_delete: None,
                    gallery_list_width: 250.,
                    splitter_last_x: None,
                    diary_column_width: 390.,
                    diary_splitter_last_x: None,
                    connected_iphone: connected_iphone_name(),
                    device_polling_started: false,
                    photo_save_directory,
                    video_thumbnails: HashMap::new(),
                    video_thumbnail_requests: HashSet::new(),
                    video_thumbnail_failures: HashSet::new(),
                    video_playback: None,
                    video_controls_visible: true,
                    video_controls_last_motion: None,
                    video_seeking: false,
                    photo_rotations: load_photo_rotations(),
                    rotated_photo_paths: HashMap::new(),
                    photo_rotation_requests: HashSet::new(),
                    photo_rotation_failures: HashSet::new(),
                    list_name_width: 360.0,
                    list_date_width: 170.0,
                    list_size_width: 100.0,
                    list_kind_width: 130.0,
                    list_column_last_x: None,
                })
            },
        )
        .expect("无法创建光屿窗口");
        cx.activate(true);
    });
}
