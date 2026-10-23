# RCC — Relative Closure Calculus（相对闭合演算）

[English](README.md) · **中文**

**"做完了"应该被计算出来，而不是被宣称。**RCC 针对一个冻结的 epoch，判定一份工作是否**相对于**已接纳的意图和上下文闭合；如果没有闭合，它会准确说出是哪一种未闭合。

## 为什么

项目里经常宣布某件事完成了："证明完成了"、"CI 绿了"、"所有目标都解决了"。这些都是断言：由做这件工作的人，相对于他心里的某个上下文做出的。当大部分工作来自自动化的 agent，这样的断言不可能逐一阅读和核对。闭合必须相对于一个固定的意图、**从证据里计算出来**；未完成的状态必须被**命名**，而不是往上取整。

RCC 的规范化器只会返回以下四者之一：
- `Closed`：相对于已接纳的意图和上下文，已经闭合；
- `Await`：还在等待具名的、尚未完成的义务；
- `Reepoch`：上下文变了，必须在新的 epoch 里重新提问；
- `Halt`：出现了矛盾，再多的工作也修补不了。

RCC 本身是 [MST-NF](https://github.com/residua-labs/MST-NF) 的一个实例：每一条说法，要么以 `Closed` 被接受，要么带着有类型的未闭合被拒绝。

## Residua 怎样使用它

- **发布时的说法：**[MST-NF](https://github.com/residua-labs/MST-NF) 的 README 里，每一句关于性质的话都通过一份说法登记表解析，由 RCC 检查；发布时的判定结果是 `Closed`。
- **风险前沿：**R-CIC 内核（[Residua](https://github.com/residua-labs/Residua)）的开放义务作为 RCC 前沿来跟踪；剩下的义务显示为 `Await`，而不是一段散文。
- **制度切割：**[IEC](https://github.com/residua-labs/IEC) 的闭合判定和快照都来自 RCC。

## 状态（准确表述）

- 本仓库是完整的 RCC Lean 开发，只排除了下文列出的三个模块：236 个库模块和 184 个测试模块，每条定理的公理都经过审计。
- **不宣称 RCC 本身已经闭合。**把它自己的义务目录（108 条）交给 RCC 检查，结果是 `Await`，有 8 个具名缺口；`closure_claim = 0`。RCC 一边被用来计算别人的工作是否闭合，一边自己的闭合还在进行中；它报告自己的方式，和报告别人的方式一样。
- RCC 属于 Residua 各版本的依赖闭包。Residua 从 **0.1** 起按版本发布（每个版本包含该版本的自举编译器、R-CIC 的当前状态和依赖闭包），见 [residua-labs/Residua](https://github.com/residua-labs/Residua)。

## 技术内容

收录内容、vendored 支撑模块、排除项、不宣称的内容、信任基和构建方法，见[英文 README](README.md) 的 *Contents* 之后各节。
