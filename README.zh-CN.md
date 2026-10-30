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

- 本仓库是完整的 RCC Lean 开发，只排除了英文 README 中 *Excluded* 一节列出的一个模块：239 个库模块和 190 个测试模块，每条定理的公理都经过审计。
- **RCC 自己的闭合同样是算出来的。**把它自己的义务目录（108 条，已随本仓库发布在 [`self-closure/`](self-closure/)）交给 RCC 的规范化器，在 literal 和 strict 两种读法下都得到 `Closed|closed=117`（原始输出与输入见 [`self-closure/verdict.txt`](self-closure/verdict.txt)）。`closed=117` 数的是可执行图的节点而不是目录条目：全图 116 个节点 —— 108 条义务加上 8 个 `disposition:*` 生产者节点（把八条具名缺口的处置接回图中）—— 计数再加上 `RCC-V2-closure` 意图节点本身。具名的保留写在目录自身里：`RC-3b`——「RCC 的自检只能管辖下一个 epoch」——是八条 `out_of_scope_documented` 处置之一。`closure_claim = 0`。
- **本次发布。**基于 Residua `main` 的 `b54a914fcf` 构建。**不再有任何定理使用 `Classical.choice`**：上一版列出的 7 条（位于 `RCC.ClosureExhaustion`、`RCC.CrossEpochFairness94`、`RCC.E2Target`、`RCC.RCC94Target`）都已重新证明，陈述逐字节不变；下面"信任基"一节的公理普查是 `scripts/PrintAxioms.lean` 的原始输出。发布前，两位来自不同模型家族的独立审计者各自通过了同样的七项检查：文件摘要、从全新构建重现公理普查、闭合判定、相对上一版的改动、普查脚本本身、卫生检查，以及本 README 中每个数字都能在原始输出里找到。
- RCC 属于 Residua 各版本的依赖闭包。Residua 从 **0.1** 起按版本发布（每个版本包含该版本的自举编译器、R-CIC 的当前状态和依赖闭包），见 [residua-labs/Residua](https://github.com/residua-labs/Residua)。

## 信任基

- 只依赖 Lean 4 核心（`leanprover/lean4:v4.14.0`），不用 Mathlib，没有其他依赖。
- 没有 `sorry`，没有 `axiom` 声明，没有 `implemented_by`、`extern` 或 `unsafe`。`native_decide` 不出现在任何定理里，只出现在 vendored 的 `RCC.Support.SlotSemanticsCore` 中 137 个 `example` 自检里（example 不导出，也没有定理依赖它们）。
- `scripts/PrintAxioms.lean` 检查 `RCC.*` 中的每一条定理（共 7,354 条，包括 `RCC.Support.*`；完整原始普查见 [`self-closure/axiom_census.txt`](self-closure/axiom_census.txt)）。精确的公理集合是：4,879 条不用任何公理；1,508 条用 `{propext}`；951 条用 `{propext, Quot.sound}`；16 条用 `{Quot.sound}`。**没有定理使用 `Classical.choice`** 或其他任何公理（特别是没有定理使用 `Lean.ofReduceBool`）。

## 构建

```sh
# 安装 elan：https://github.com/leanprover/elan
lake build                                   # 构建 RCC 和 RCCTests
lake env lean --run scripts/PrintAxioms.lean # 输出全部 RCC 定理的公理汇总
```

## 技术内容

收录内容、vendored 支撑模块、排除项和不宣称的内容，见[英文 README](README.md) 的 *Contents* 之后各节。

## 许可

Apache-2.0，见 `LICENSE` 与 `NOTICE`。
