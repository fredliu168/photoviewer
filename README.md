# 光屿

光屿是一款面向 macOS 的本地照片与视频管理应用，也可以用日记整理生活记录。应用使用 Rust 和 GPUI 构建。

## 功能

- 浏览和筛选照片、视频，支持多种图库布局。
- 预览照片与播放视频，查看照片拍摄信息并旋转照片。
- 创建分类日记，编辑标题、正文和主题分类。
- 将照片或视频拖入日记，在编辑模式中调整媒体顺序，也可以拖出日记。
- 日记照片轮播、实况照片配对播放、回收站恢复与彻底删除。

## 运行

需要 macOS、Rust 工具链和 Xcode Command Line Tools：

```sh
cargo run
```

使用 `cargo bundle --release --format osx` 可生成 macOS 应用包。

## GitHub Release

推送 `v` 开头的标签（例如 `v0.1.0`）会自动构建 Apple Silicon（ARM64）版 macOS 应用，并将 `guangyu-macos-arm64.zip` 发布到 GitHub Release。也可以在 Actions 页面手动运行 `macOS Release`；不填写标签时会生成可下载的 workflow artifact，填写标签时会创建对应 Release。
