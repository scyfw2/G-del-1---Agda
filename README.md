# godel-agda-full

这是一个更完整的 Agda 工程，用来形式化哥德尔第一不完备性定理的证明结构。

它不依赖 `agda-stdlib`，只使用 Agda builtin：`Nat`、`List`、`Equality`。

> 注意：如果本地没有安装 `agda`，请先安装 Agda；代码可以用下面的命令检查。

For an English walkthrough of the proof architecture, see
[`docs/proof-guide.md`](docs/proof-guide.md).

## 文件结构

```text
Godel/Core.agda
  空类型、否定、乘积、Σ、等式辅助引理。

Godel/Syntax.agda
  一阶算术对象语言：项、公式、de Bruijn 变量、重命名、替换、numeral。

Godel/Coding.agda
  项/公式的 Gödel 编码函数，proof predicate 的对象语言表示：
    ProofOf p A = “p 是公式 A 的证明码”。
  还包含 noProofs、someProof、noProofsTemplate 以及替换计算引理。

Godel/CanonicalCoding.agda
  可解码的结构化/数值化语法编码层、fuelled decode round-trip 引理、
  unfuelled decode round-trip/no-junk 引理、diagFormula/DiagCode/DiagRel 基础。

Godel/DecidableCoding.agda
  自然数、项、项列表、公式的布尔相等检查器、反身性和 soundness 证明。

Godel/DiagonalCoding.agda
  canonical 数值编码上的 Subst0NatCode/DiagNatCode 图关系，
  以及未来对象语言表示性目标 Subst0Rel。

Godel/ComputableGraphs.agda
  使用 canonical decoder 和布尔相等定义 checked substitution/diagonal graph，
  并证明 checked graph soundness 以及到 Σ graph 的桥接。

Godel/PrimitiveRecursive.agda
  arity-indexed primitive recursive functions/relations 的语法和解释函数。
  `PRF` 的 data constructors 只保留 zero/suc/proj/comp/prec。

Godel/PRRepresentability.agda
  PA 表示 primitive recursive functions/relations 的接口，
  并给出最小基 PRF/PRRel 的结构递归表示性闭包入口；
  composition 使用中间 graph 合取；基础 primitive recursion closure 保持兼容，
  PA-history 版本由 PRHistoryFormula 单独给出。

Godel/PRBooleanHelpers.agda
  加法、乘法、前驱、isZero、not、and、or 等基础 PR helper。

Godel/PRSequenceCoding.agda
  primitive recursion 的完整 PA 表示性证明所需的 sequence coding 接口，
  包括 seqLength/seqNth/history-valid 的 correctness 和 substitution 稳定性义务。

Godel/PRHistoryCoding.agda
  primitive recursion 的 meta-level history、historyCode、historyLength、
  historyNthDefault 以及 evalHistory 的基础引理；historyCode 现在使用
  可 fuelled round-trip 的 canonical nat-list 编码。

Godel/PRHistoryFormula.agda
  PA 内部递归历史公式入口：historyResultFormula 具有 ∃s、seqLength、
  history-valid、seqNth 约束；同时提供 history-backed closure 的桥接版本
  和纯 history formula closure 的 uniqueness 目标。

Godel/PRConcreteSequenceCoding.agda
  concrete sequence coding 的 PRF 候选和 correctness obligations；
  目前不伪造无条件 concretePRSequenceCoding。

Godel/PRConcreteHistoryValid.agda
  concrete history-valid checker 的 PRF 候选，以及从 sequence/history
  obligations 组装 PRPrimitiveRecursionInfrastructure 的 adapter。

Godel/CanonicalCodePR.agda
  canonical code tree/list destructors 的 PR helper 入口和表示性包装。

Godel/SyntaxCodingPR.agda
  记录 canonical syntax coding、decode、formulaEq、subst0、diag
  被 primitive recursive relations 精确刻画所需的证明目标。

Godel/SyntaxCodingPRDerived.agda
  将 canonical decode、formulaEq、subst0、diag checker 作为 derived PRF
  definitions 暴露。当前版本依赖旧 checker 思路，等待下一阶段用真正
  numeric PR decoder 重建。

Godel/SyntaxCodingPRCheckers.agda
  将 canonical decode、formulaEq、subst0、diag checker 暴露为 PR relations。

Godel/SyntaxCodingPRSoundness.agda
  证明这些 PR checker 与现有 executable checked graph 层 sound/complete。

Godel/SyntaxCodingPRInstances.agda
  将 SyntaxCodingPR 及其 PR relation 表示性打包成 PACheckedGraphPRInputs。

Godel/SyntaxCodingPRConcrete.agda
  旧 concrete SyntaxCodingPR 实例文件；当前不由 Everything 导入，
  等待下一阶段在无 evaluator oracle 的前提下重建。

Godel/RepresentabilityTargets.agda
  Subst0Rel/DiagRel 表示 graph 目标的通用接口，
  以及 checked/un-checked 的 PrePARepresentabilityData 聚合边界。

Godel/NoProofsDiagonalization.agda
  noProofs 专用 diagonal helper formula、candidate 公式，
  以及 candidate 落在 DiagNatCode 图中的证明。

Godel/ProofSystem.agda
  参数化 Hilbert 风格证明系统 Derives Ax A。

Godel/PA.agda
  PA 的基本非逻辑公理和归纳 schema 的语法表示。

Godel/PAObjectLogic.agda
  PA 内部等式推理和函数同余能力的接口。

Godel/PAObjectLogicProofs.agda
  从 proof system 的等式逻辑规则构造真实的 PAObjectLogic 和 PAProofInfrastructure。

Godel/PAClosedArithmetic.agda
  PA 对闭 numeral 加法、乘法、后继非零事实的计算接口，
  以及 PAProofInfrastructure 聚合入口。

Godel/PAClosedArithmeticProofs.agda
  在 PAObjectLogic 假设下，从 PA 公理推出闭 numeral 算术接口。

Godel/ProofCoding.agda
  PA 证明树的编码：codePAProof，以及具体 ProofCodePA 关系。

Godel/ArithmetizedTheory.agda
  “已经算术化的理论”接口：可证性、proof-code 完备/可靠、proof predicate 表示性、ω-一致性。

Godel/Diagonal.agda
  对角化/不动点引理接口，并从 noProofsTemplate 的不动点构造 GödelSentence。

Godel/Original.agda
  Gödel 原始版本：一致性 + ω-一致性推出 Gödel 句及其否定都不可证。

Godel/Rosser.agda
  Rosser 版本接口：一致性推出 Rosser 句及其否定都不可证。

Godel/PAFirstIncompleteness.agda
  将 PA 语法、PA 证明编码、表示性假设、对角化假设组合起来，得到 PA 版本的第一不完备性定理。

Godel/PARepresentabilityEntry.agda
  PA 入门层：直接以 PA-provable 表达 checked graph 表示性义务，
  并提供到 CheckedPrePARepresentabilityData 的 adapter。

Godel/PACheckedGraphTargets.agda
  将 PA checked graph 表示性拆成 decode、formulaEq、subst0、diag
  四类更小目标，并从这些目标组装 PACheckedGraphRepresentability。

Godel/PACheckedGraphPRTargets.agda
  primitive-recursive 路线的 checked graph 目标形状：用显式算术公式
  builders 替代未解释 Rel 符号作为最终 PA 表示性目标。

Godel/PACheckedGraphPRProofs.agda
  从 SyntaxCodingPR 和 PR relations 的 PA 表示性组装 PR checked graph target。

Godel/AbstractOriginal.agda, Godel/AbstractRosser.agda
  旧版更小的抽象证明骨架，也保留下来。
```

## 本地检查

```bash
cd godel-agda-full
agda -i . Godel/Everything.agda
```

也可以分模块检查：

```bash
agda -i . Godel/Syntax.agda
agda -i . Godel/Coding.agda
agda -i . Godel/PAFirstIncompleteness.agda
```

## 证明主定理在哪里？

### 抽象算术化理论版本

`Godel/Original.agda`：

```agda
first-incompleteness : Consistent T → OmegaConsistent T → Undecidable T G
```

其中 `G` 来自 `Godel.Diagonal.GödelSentence T`。

### 从对角化引理直接得到 Gödel 句

`Godel/Original.agda` 里的：

```agda
module FromDiagonal (T : ArithmetizedTheory) (DL : DiagonalLemma T) where
  GSentence : GödelSentence T
  first-incompleteness : Consistent T → OmegaConsistent T → Undecidable T G
```

### PA 版本

`Godel/PAFirstIncompleteness.agda`：

```agda
PA-first-incompleteness :
  (D : PAIncompletenessData) →
  Consistent (PA-as-theory (PAIncompletenessData.repr D)) →
  OmegaConsistent (PA-as-theory (PAIncompletenessData.repr D)) →
  Undecidable (PA-as-theory (PAIncompletenessData.repr D)) (PA-GödelFormula D)
```

## 哪些地方仍是标准大引理？

这个工程已经把以下内容写成了具体 Agda 结构：

- 一阶算术语法；
- de Bruijn 替换；
- Gödel 编码函数；
- PA 公理 schema；
- Hilbert 风格证明树；
- PA 证明树编码 `codePAProof`；
- Gödel 句推出不可判定性的核心证明；
- Rosser 版本的核心证明。

但真正把 PA 的全部元数学完全展开，还需要完成几个经典大引理：

1. **表示性引理**：PA 能表达 proof-checker 的正例和反例。
2. **对角化/不动点引理**：对任意一元公式 φ，PA 能构造并证明 θ ↔ φ(⌜θ⌝)。
3. **Syntax checker 最小基展开**：当前 `PRF` 的 constructor 和 evaluator
   已收紧为 `zero/suc/proj/comp/prec` 的最小基，PR 表示性入口也改为
   结构递归闭包；composition graph 已脱离 closure 的
   `evaluatedGraphFormula`。primitive recursion 现在另有 PA-history 公式
   入口，显式包含 ∃s、sequence length、history-valid、nth 约束；当前
   history-backed closure 仍用 evaluated 左支撑处理唯一性，下一步是把这个
   左支撑替换为 sequence-coded history uniqueness。historyCode 已改成可
   round-trip 的 canonical nat-list 编码；sequence/history concrete 模块
   现在列出 PRF 候选和必须补齐的 correctness obligations，但不会把这些
   obligations 当作已证明实例。之后再用真正的 numeric PR decoder 重建
   `SyntaxCodingPRConcrete`，并把 proof predicate checker 纳入同一路线。

在本工程中，这两个部分以 record 字段给出：

```agda
record PARepresentability : Set₁ where ...
record DiagonalLemma (T : ArithmetizedTheory) : Set where ...
```

只要补齐这两个 record 的实例，`PA-first-incompleteness` 就直接给出 PA 的第一不完备性结论。
