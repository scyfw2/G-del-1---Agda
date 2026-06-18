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
  diagFormula/DiagCode/DiagRel 基础。

Godel/ProofSystem.agda
  参数化 Hilbert 风格证明系统 Derives Ax A。

Godel/PA.agda
  PA 的基本非逻辑公理和归纳 schema 的语法表示。

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

但真正把 PA 的全部元数学完全展开，还需要证明两个经典大引理：

1. **表示性引理**：PA 能表达 proof-checker 的正例和反例。
2. **对角化/不动点引理**：对任意一元公式 φ，PA 能构造并证明 θ ↔ φ(⌜θ⌝)。

在本工程中，这两个部分以 record 字段给出：

```agda
record PARepresentability : Set₁ where ...
record DiagonalLemma (T : ArithmetizedTheory) : Set where ...
```

只要补齐这两个 record 的实例，`PA-first-incompleteness` 就直接给出 PA 的第一不完备性结论。
