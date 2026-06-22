# godel-agda-full

这是一个更完整的 Agda 工程，用来形式化哥德尔第一不完备性定理的证明结构。

它不依赖 `agda-stdlib`，只使用 Agda builtin：`Nat`、`List`、`Equality`。

> 注意：如果本地没有安装 `agda`，请先安装 Agda；代码可以用下面的命令检查。

For an English walkthrough of the proof architecture, see
[`docs/proof-guide.md`](docs/proof-guide.md).

## Lean shadow proof

本仓库现在包含一个独立的 Lean 4 shadow prototype：

```text
LeanShadow/
```

它不是 Agda formalization 的迁移，也不是低层编码证明的 Lean 重证。它把
Agda 中已经完成或正在推进的低层工作声明为显式 interface/axiom，然后在 Lean
里检查高层依赖链：

```text
ProofCodePA is PR
→ PA represents ProofCodePA
→ diagonal/noProofs fixed point
→ first incompleteness theorem
```

可以用下面命令检查：

```bash
lake build LeanShadow
```

入口 theorem 在 `LeanShadow/FirstIncompleteness.lean`。其中
`ProofCodePAPRData` 是 Agda 主线最终要提供的证明检查器 PR 数据；Lean shadow
证明展示：一旦这个数据存在，就能通过 PA 表示所有 PR 关系、noProofs fixed
point 和抽象不完备性定理得到 Gödel 句不可判定。

`LeanShadow/Rule37Mini.lean` 是一个 rule37 小型实验：它使用简化的 pair-based
code，而不是 Agda 的 canonical base-4 code，证明了 witness checker 与 bounded
search 的 sound/complete 骨架。该实验保留 `fst_pair`、`snd_pair`、`pair_eta`
和 `witnessBound` 为显式接口，正好对应 Agda 主线里 canonical parser
correctness 和 witness bound 需要承担的部分。

`LeanShadow/Rule37CanonicalMini.lean` 进一步用一个 toy canonical code 完成这些
接口形状：证明 parser completeness/soundness、从 canonical parser target 推出
closed rule37 code equality，以及 witness bound。它仍不是 Agda base-4 编码的
替代证明，但说明 Lean 对这类 parser/equality/bound proof skeleton 的自动化
比较顺手。

`LeanShadow/Rule37Base4Mini.lean` 再进一步使用 base-4 digit stream toy model：
natural payload 用若干 digit `2` 加终止 digit `0` 编码，atom 用 tag digit `1`，
rule37 node 用 tag digit `3` 加 unary tag payload 和两个 atom children。该模块
证明了 base-4 parser 的 complete/sound、从 parser success 推出 canonical
digits/code equality，以及 witness bound by digit length。它仍比 Agda 的完整
canonical code 简化，但已经更接近当前 rule37 parser/search 的真实证明形状。

`LeanShadow/CodeListLengthMini.lean` 是针对当前 Agda 缺口的更小实验：
它定义了 base-4-ish `Code` / `List Code` 编码、fuelled code-list parser、
`codeListLengthCheck`，并证明 complete、sound 和 nonzero-sound。这个文件没有
关闭 Agda 的 `code-list-length-pr`，但给出了一条可移植的证明模式：先证明
with-rest parser 的 “fuel 大于编码长度则成功”，再证明 parser soundness，最后
把 `checker ≠ 0` 转成 code-list-length 语义事实。

`LeanShadow/CodeListLengthScannerMini.lean` 再把这个缺口推进一层：它定义一个
不构造 `Code` 树的 scanner，只跳过 encoded nat/code 并计算 code-list length，
然后证明 scanner checker 与 `codeListLengthCheck` 完全一致。这说明 Agda 里的
concrete PRF 不必重建语法树；它可以实现这个 scanner，再证明 evaluator 等于
scanner checker。

`LeanShadow/CodeListLengthStackMachineMini.lean` 把 scanner 再改写成更接近
PRF 的状态机骨架：有限控制栈、逐 digit transition、以及 base-5 encoded stack
的 push/top/tail 定理。它没有声称已经证明 Agda 的
`evalPRF lengthScannerF = codeListLengthScannerCheck`；它给出的可搬运经验是：
Agda 里的 concrete PRF 应把状态编码为自然数，并实现 stack transition，而不是
构造 `List Code`。该模块现在还证明了 canonical completeness：对
`encodeCodeListWithRest codes []`，逐 digit stack machine 返回 `codes.length`。
它还包含 numeric-state valid-step bridge：encoded input rest 和 encoded stack
上的每个有效 transition 都对应 explicit stack-machine transition，并证明了
prefix-length fuel induction：只运行当前 encoded nat/code/list prefix 的长度，
会留下 suffix 而不误消费后续输入。Lean shadow 还加入了
`stateStepEval_eq_stepNumStable` 以及 root/nested/code/nat、失败态、完成态的
逐分支 theorem：它确认 PRF 层 `stateStepF` 应对接的是完成态稳定的
`stepNumStable`，而不是只适合 exact-prefix run 的 `stepNum`。Agda 现在已经
搬入 branch-wise `stateStepF` bridge：`CanonicalCodeListLengthStateStepBranches`
证明了 root/nested/code/nat 的有效分支从 PRF evaluator 落到对应 numeric
stable transition。Lean shadow 进一步证明了 `runStateStepEvalFuel` 的
prefix+extra fuel induction：跑完 canonical code-list prefix 后，额外 fuel
停在完成态。`LeanShadow/CodeListLengthNumericEvalMini.lean` 现在还证明了
canonical bound `prefix length ≤ suc encoded-input`：路线是先用
`codeSize` / `codeListSize` 控制 digit 长度，再证明 closed numeric code 至少支付
`2 * codeListSize`。因此 Lean 侧已经导出固定 fuel `suc input` 的 canonical
completeness。Agda 侧目前有对应的 conditional bridge
`lengthScannerWithFuelOpaqueF-codeList-complete-fixed-from-bound`；下一步是把这个
size bridge 搬到 Agda，然后再处理 arbitrary-input soundness。

## 当前 PR 表示性状态

PA represents all PR functions/relations 的第二步已经有最终 public boundary：

```text
final entry   = Godel.PRRepresentabilityFinal
legacy bridge = Godel.PRRepresentability
```

新高层模块应优先使用 `Godel.PRRepresentabilityFinal.prf-represented` 和
`Godel.PRRepresentabilityFinal.prrel-represented`。旧 `Godel.PRRepresentability`
仍保留给低层 bootstrap 和兼容代码。

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
  PA 表示 primitive recursive functions/relations 的外部接口和旧兼容
  implementation。旧 `prf-represented` 仍保留为 bridge；新的推荐 theorem
  入口在 PRRepresentabilityFinal。

Godel/PRGraphSubstitution.agda
  binder-safe graph 路线需要的替换引理：subst0 会消去 wkTerm/wkVec。

Godel/PRStructuredRepresentability.agda
  substitution-stable 的结构化 PR function 表示性接口。它把 uniqueness
  升级到任意 term inputs，并加入 graph-input congruence、general graph
  substitution、输出变量替换稳定性、
  nested-exists 前缀工具，以及 zero/suc/proj 的基础实例；composition 已经通过
  nested-exists lifting 完成结构化 closure，并导出
  `structured-composition-closes`。

Godel/PRBooleanHelpers.agda
  加法、乘法、前驱、isZero、not、and、or 等基础 PR helper。

Godel/PRVectorHelpers.agda
  arity-indexed PRF 投影向量 helper，用于在任意 arity 下从
  `(x , s , xs...)` 这类输入中取出 tail 参数。

Godel/PRBoundedSearch.agda
  最小基 PRF 的常量函数 helper。

Godel/PRArithmeticSemantics.agda
  基础 PR helper 的 meta-level 语义证明，把 evalPRF 连接到干净的
  Agda 自然数函数。

Godel/PRDigitCoding.agda
  base-4 数字层的 derived PRF：mod4、div4、按位置取 digit，以及
  appendDigitF 这个 canonical digit 构造端 helper。

Godel/PRDigitSemantics.agda
  mod4/div4/iterated-div4/digitAt/appendDigitF 的语义镜像，以及
  appendDigit 与 mod4/div4 的 head/tail 引理。

Godel/PRNatListDecoder.agda
  基于 digit 计数的 nat-list decoder PRF 候选，包括 seqLengthF 和 seqNthF。

Godel/PRNatListDigitStream.agda
  historyCode 的 finite digit stream 视图，证明编码对应、非零 digit 的完整
  计数、seqNth active scanner 的超界稳定性，以及 nat-list 上的最终 nth
  归纳定理。

Godel/PRNatListDecoderSemantics.agda
  seqLengthF/seqNthF 的 evalPRF-to-meta 语义证明；seqLength 已连接到
  historyLength，seqNth 已连接到 finite digit stream 的 active scanner 语义。

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

Godel/PRStructuredHistoryFormula.agda
  structured primitive-recursion route 的 history formula 层：给出
  substitution-stable 的 sequence/history formula shell、derived
  structured-history-body-subst0，以及 historyResultFormula 的 value 和
  substitution lemmas。

Godel/PRHistoryUniqueness.agda
  sequence-coded history uniqueness 入口，并导出
  structured-primitive-recursion-closes。该 theorem 的 graph formula 只使用
  structuredHistoryResultFormula，不再包含 evaluatedGraphFormula。

Godel/PRStructuredTheorem.agda
  将 zero/suc/proj、structured composition closure 和 structured primitive
  recursion closure 汇总成最小基结构递归 theorem，导出推荐的
  prf-represented / prrel-represented。这里的 relation formula 使用
  characteristic function 的真实 graph formula，而不是 evaluated graph。

Godel/PRRepresentabilityFinal.agda
  第二步的最终 public boundary：re-export PR 表示性接口，并把
  PRStructuredTheorem 的 prf-represented / prrel-represented 暴露为推荐入口；
  同时打包 paAllPRRepresentability。

Godel/PRFunctionGraph.agda
  通用函数图桥：把任意 `f : PRF n` 转成 `functionGraphRel f : PRRel (suc n)`，
  其语义是 `output = f(inputs)`。该 relation 通过
  `PRRepresentabilityFinal.prrel-represented` 自动获得 PA 表示性，并提供
  sound/complete 引理。后续 parser/checker 的函数型 destructor 都会用这层接入
  relation target。

Godel/PRConcreteSequenceCoding.agda
  concrete sequence coding 的最小基 PRF 候选、seqLength/seqNth correctness
  证明，以及无条件导出的 concretePRSequenceCoding 实例。

Godel/PRHistoryValidCheckers.agda
  history-validF 的最小基 PRF checker：检查 length、初值和 bounded step。

Godel/PRHistoryValidSemantics.agda
  history-validF 的 semantic mirror，证明 checker 等于干净的 meta-level
  historyValidNat，并证明真实 evalHistory 被 checker 接受。

Godel/PRConcreteHistoryValid.agda
  concrete history-valid checker 的 legacy adapter；旧
  PRPrimitiveRecursionInfrastructure bridge 仍保留 history-body
  substitution-stability obligation。新的 structured route 通过
  PRStructuredHistoryFormula 派生对应 substitution lemma，不依赖这个
  obligation。

Godel/CanonicalCodePR.agda
  canonical code tree/list destructors 的 PR helper 入口和表示性包装。
  当前 atom/node head tag checker 已由 base-4 digit helper 实现并带有
  head sound/complete 引理；atom payload 和 node tag 也已改为 prefix-nat
  decoder PRF，并有 eval-to-meta correctness 与 canonical correctness。
  node children 也已由 prefix-nat rest extractor 实现并证明 canonical
  correctness；code-list nil/cons tag checkers 已由 digit helper 实现。
  同时新增了 builder 侧基础：encodeNatWithRestF、atomCodeWithRestF、
  atomCodeF、nodeCodeWithRestF、numeralTermCodeWithRestF，以及 closed numeral
  equality/inequality formula-code builders；它们都有对 canonical encoding 的
  correctness 和 PA representability 包装。
  code-list head/tail/length/nth 仍是后续 proof checker PR 化要补的解析型
  destructor；它们的 function-graph PRRel 入口已通过 `PRFunctionGraph` 暴露。

Godel/CanonicalCodeParserTargets.agda
  self-delimiting canonical code parser 的 numeric target 层，定义
  CodeWithRestNat、CodeSkipNat、CodeListHeadNat、CodeListTailNat、
  CodeListLengthNat、CodeListNthNat 等规格。后续 `codeListHeadF` / `codeListTailF` /
  `codeListLengthF` / `codeListNthF` 的 PRF correctness 会对准这些 targets。
  同时定义 `CanonicalCodeParserPR`，把 code-with-rest、skip-code 和 list
  parser 的 sound/complete obligations 收束为 PRRel record，并通过
  `PRRepresentabilityFinal.prrel-represented` 给出 PA 表示性 adapter。

Godel/CanonicalCodeParserSemantics.agda
  canonical code-list parser 的 executable meta-level semantic mirror：
  使用现有 `decodeCodeWithRest` / `decodeCodeListWithRest` 定义
  code-with-rest、skip-code 以及 list head/tail/length/nth 的 Maybe 语义，
  并证明 canonical completeness 以及 soundness 回到
  `CanonicalCodeParserTargets`。
  后续真正的最小基 PRF parser 将对准这一层。

Godel/CanonicalCodeListLengthCheck.agda
  将 Lean `CodeListLengthMini` 的证明骨架搬回 Agda：定义
  `codeListLengthCheck`，证明它对 `CodeListLengthNat` 的 complete、sound 和
  nonzero-sound，并提供 `CodeListLengthPRCandidate` /
  `codeListLengthNonzeroSound-from-check` adapter。它仍不是 concrete
  `code-list-length-pr` 的最小基 PRF 实现；它把剩余任务精确压缩为：
  构造一个 PRF，并证明其 evaluator 等于 `codeListLengthCheck`。

Godel/CanonicalCodeListLengthScanner.agda
  将 Lean scanner route 搬回 Agda：定义 `skipCodeWithRestFuel` 和
  `scanCodeListLengthWithRestFuel`，证明 scanner 与现有 `decodeCodeWithRest` /
  `decodeCodeListWithRest` 一致，并推出 `codeListLengthScannerCheck ≡
  codeListLengthCheck`。下一步 concrete PRF 可以对准这个 scanner，而不是对准
  会构造 `List Code` 的 full decoder。模块还提供
  `CodeListLengthScannerPRCandidate` 和 `scannerCandidate->checkCandidate`，
  把最终 PRF obligation 固定为 evaluator 等于 scanner checker。

Godel/CanonicalCodeListLengthStackMachine.agda
  将 Lean stack-machine completeness 归纳搬回 Agda 的 explicit digit-stream 层：
  定义 meta-level `Frame` / `MachineState` / `stepState` / `runState`，并证明
  `parseCodeListLengthStackMachine-complete`。这不是最终 numeric PRF theorem，
  但它给出后续证明 `stateStepF` correctness 和 fuel induction 的结构模板。

Godel/CanonicalCodeListLengthNumericState.agda
  将 Lean numeric-state valid-step bridge 搬回 Agda：定义 encoded input rest、
  base-5 encoded stack、numeric `stepNum`，并证明 root/nested/code/nat 的有效
  branch equations，以及 prefix-length fuel induction。也就是说，numeric
  meta-state 已经证明只跑当前 encoded nat/code/list prefix 的长度会留下 suffix。
  该模块还定义 `stepNumStable`，使完成态 `(rest=0, stack=0, ok=true)` 保持不动；
  它现在是 `stateStepF` evaluator correctness 的直接 meta-level 目标，并已包含
  失败态、完成态、empty-stack nonzero 的稳定边界引理。

Godel/CanonicalCodeListLengthStatePR.agda
  将 Lean encoded-stack state-machine route 搬回 Agda 的 PRF 层：定义真正的
  `lengthScannerF : PRF 2`。它用 `precF` 跑 `suc list-code` 步，状态编码为
  canonical nat-list `[rest, stack, len, ok]`，stack 用 base-5 cell。模块已证明
  state constructor/projection 的 round-trip 小引理，并补齐
  `ifBoolF/ifEqF`、`mod5F/div5F`、`pushFrameF` 以及 state 派生字段的 evaluator
  correctness。

Godel/CanonicalCodeListLengthStateStepBranches.agda
  将 Lean 的逐分支 theorem 搬回 Agda：通过泛型 `ifBoolF/ifEqF` selector lemma
  避免巨大 branch 展开，并证明 `stateStepF` 在 root/nested/code/nat 的有效
  digit 分支上对应 numeric stable transition。失败侧也已经按同样结构补齐：
  root/nested/code/nat 的无效 digit 分支会进入 failed state，失败态稳定、
  done 态稳定、empty-stack/nonzero-rest 会失败。这些 lemma 都在 selector
  层证明并以 opaque wrapper 暴露，避免 fuel induction 反复展开整个
  `stateStepF`。

Godel/CanonicalCodeListLengthStateFuel.agda
  固定下一步 fuel induction 的 Agda runner：`runStateStepFuel`、加法分解
  `runStateStepFuel-add`、以及 canonical state-code 形状。

Godel/CanonicalCodeListLengthStateFuelNat.agda
Godel/CanonicalCodeListLengthStateFuelCode.agda
Godel/CanonicalCodeListLengthStateFuelCodeList.agda
Godel/CanonicalCodeListLengthStateFuelFailure.agda
  将 Lean 的 prefix-length fuel induction 搬回 Agda PRF 层。证明分成三层：
  unary nat prefix、code-frame branch/atom prefix、以及 mutual code/code-list
  prefix theorem。关键结论是 `stateStepF` 跑完当前 canonical nat/code/list
  prefix 后正好留下 suffix，不会继续误跑 suffix。失败侧 fuel induction
  也已搬回：failed/done 状态稳定，empty-stack/nonzero-rest 进入并保持失败。
  下一步是把 canonical prefix theorem 和 failure-side theorem 组合成最终
  scanner evaluator equation：
  `evalPRF lengthScannerF (args₂ list-code len) ≡ codeListLengthScannerCheck list-code len`。

Godel/CanonicalCodeNodeTargets.agda
  proof checker 外层 node parser 的 numeric target：`NodeCodeNat input tag children-code`
  表示 `input` 是 tag 为 `tag`、children list code 为 `children-code` 的
  canonical node。并给出 `CanonicalCodeNodeParserPR` 和 PA 表示性 adapter。

Godel/CanonicalCodeNodeSemantics.agda
  node parser 的 executable semantic mirror：用 `decodeCode` 解析 raw code，
  只接受 `node tag children`，并证明 canonical completeness 和 soundness
  回到 `NodeCodeNat`。

Godel/CanonicalCodeNodeParserFromListLength.agda
  full `NodeCodeNat` parser 的轻量 bridge。它把 node builder equality 与
  code-list-length parser 组合起来：只要已有 `CanonicalCodeParserPR` 的
  `code-list-length-pr` 以及对应 nonzero-sound，就能导出完整
  `CanonicalCodeNodeParserPR`。因此 node parser 本身不再是 rule37 的
  monolithic 缺口；剩余缺口被进一步缩到 concrete code-list-length parser。

Godel/CanonicalCodeRawNodePR.agda
  proof checker 外层 node parser 的 concrete PR 入口。它定义
  `RawNodeCodeNat` 和 `rawNodeCodePR`，检查 input 是 node 头，并且
  `nodeTagF` / `nodeChildrenF` 抽出的 tag 与 children-code 等于给定值；
  同时证明 sound/complete 和 PA representability。它故意弱于完整
  `NodeCodeNat`：children-code 是否为 canonical code list 仍留给后续
  code-list parser。

Godel/CanonicalCodeRawListPR.agda
  canonical code-list parser 的第一层 concrete PR 分支。它把已有
  `codeListNilF` / `codeListConsF` 包装为 `rawCodeListNilPR` /
  `rawCodeListConsPR`，证明 nil/cons head digit 的 sound/complete、canonical
  complete，以及 PA representability。真正的 head/tail/length/nth payload
  parser 仍是下一步。

Godel/CanonicalCodeRawAtomListPR.agda
  code-list cons 的 atom-head concrete PR 分支。它检查 list-code 是 cons，
  第一项是 `atom n`，并抽出 head atom code 和 tail list code；同时证明
  sound/complete、canonical complete 和 PA representability。这个分支直接
  服务 rule37 等 proof-rule payload 解析，但仍弱于完整任意 code-list
  head/tail parser。

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

Godel/ProofCanonicalCoding.agda
  可解码的 canonical PA proof-tree 编码层：canonicalDerivationCode、
  canonicalCodePAProof、CanonicalProofCodePA，以及 proof-code round-trip
  入口。它是后续 PR proof checker 的输入编码基础。

Godel/ProofCanonicalChecker.agda
  canonical proof-tree code 的 executable checker：从 proof code 计算结论公式，
  并证明 canonicalCodePAProof 生成的真实 PA proof 会被 checker 接受；
  反向也已证明到 PA-provable，即 checker 接受某公式时能重建 PA 证明。
  `ExecutableProofCodePA` 是后续 PR relation 要精确表示的语义规格；
  `DecodedExecutableProofCodePA` 把这个规格等价改写为“数值 code 解码出
  canonical proof tree，且 code-level checker 接受”。

Godel/ProofCheckingPR.agda
  executable canonical proof checker 的 primitive-recursive 目标层：固定
  proofCodePAPR : PRRel 2、相对于 `ExecutableProofCodePA` 的 sound/complete
  义务、通过
  PRRepresentabilityFinal.prrel-represented 得到 PA 表示性，并记录 canonical
  proof-checker formula、旧 ProofCodePA 和旧 ProofOf 之间仍需证明的 bridge。
  这个 bridge 不假设旧 proof code 和 canonical proof-tree code 是同一个数。

Godel/ProofCheckingPRTargets.agda
  proof checker 的全数值 PR target 层：定义 `ExecutableProofCodeNat` 和
  `DecodedExecutableProofCodeNat`，证明二者等价，并提供 adapter 把 numeric
  / decoded PR checker data 转成 theorem-facing `ProofCheckingPR`。

Godel/ProofCheckingPRComponents.agda
  proof checker 的可复用 concrete PR component。当前已实现公式码/自然数码
  相等组件：`formulaCodeEqPR = rel eqNatF`，证明 sound/complete，并通过
  `PRRepresentabilityFinal.prrel-represented` 明确给出 PA 表示性。还新增
  fixed tag equality：`tagEqPR expected`，用于后续 proof-step checker
  匹配 `node 0` 到 `node 38` 这类 rule tags；以及 `zeroTestPR`，用于
  空分支、失败码和基础布尔条件的 zero-test。`andPR = rel andF` 也已
  给出 sound/complete 和 PA 表示性，用来组合 proof-step checker 条件；
  `orPR = rel orF` 也已完成，刻画“至少一个输入非零”的分支条件。
  `natNeqPR` 刻画自然数不等，用于 canonical proof checker 的 closed
  numeral inequality rule。

Godel/ProofCheckingBranch.agda
  proof checker branch 的通用聚合层。一个 branch 只要能从 `PRRel-holds`
  或 nonzero hit 恢复 `DecodedExecutableProofCodeNat`，就可以通过
  `orProofCheckingBranchPR` 安全组合。`TargetedProofCheckingBranchPR` 还把
  每个 branch 的 semantic target 与 completeness 分开记录，并提供
  `fixedCodeLeafTargetedBranch` 作为固定 proof-code/formula-code leaf 的
  opaque 入口；`targetedProofCheckingBranch-map` 和
  `targetedProofCheckingBranch-to-decodedPR` 则在 target 覆盖完整
  `DecodedExecutableProofCodeNat` 时直接生成 `ProofCheckingPRDecodedNat`。
  另有 `targetedProofCheckingBranch-covered-proofCheckingPR`，可把覆盖完整
  decoded checker 的 branch 直接送到 theorem-facing `ProofCheckingPR`。
  `ProofCheckingBranchExtensionData` 是增量扩展接口：给定一个已有 targeted
  branch、一个新增 targeted branch，以及合并 target 的 decoded coverage proof，
  就能继续导出 `ProofCheckingPRDecodedNat` / `ProofCheckingPR`。
  这个模块是最终 `proofCodePAPR` OR 树的胶水；固定 PA 公理叶子族的完整
  聚合仍需先加 opaque 边界，避免一次性归约多个大型 canonical
  proof/formula code。

Godel/ProofCheckingFixedLeafBranches.agda
  固定 proof-code/formula-code leaves 的参数化 OR 聚合器。它提供
  `fixedLeafTargetedBranch₂`、`fixedLeafTargetedBranch₄` 和
  `fixedLeafTargetedBranch₆`，只接收 `FixedCodeLeafData` 参数，不导入具体
  PA axiom constants。这样六个固定 PA 公理 leaf 可以先作为 opaque 数据传入，
  再聚合成 targeted branch，避免在聚合层展开大型 canonical code。

Godel/ProofCheckingRule37Branch.agda
  rule37 的 proof-checking branch adapter。`ProofRule37PR` 本身只给
  `eval = 1` 的 soundness；进入最终 OR 树还需要 nonzero hit soundness。
  本模块用 `ProofRule37CheckingBranchData` 明确记录这个额外字段，并导出
  `proofRule37TargetedBranch : TargetedProofCheckingBranchPR ClosedNumeralNeqRuleNat`。
  因此 canonical witness search 一旦完成并给出 nonzero soundness，就能直接成为
  `proofCodePAPR` 的一个 targeted branch。

Godel/ProofCheckingBranchBundle.agda
  proof checker OR 树的轻量 bundle。它把六个 opaque `FixedCodeLeafData`
  leaf 和一个 `ProofRule37CheckingBranchData` 组合成 targeted branch，并在调用方
  提供 full decoded checker coverage 时导出 `ProofCheckingPRDecodedNat` 或
  theorem-facing `ProofCheckingPR`。它仍不导入具体 PA axiom constants，保持
  fixed-leaf 聚合的性能边界。`ProofCheckingFixedAndRule37Data` 是后续填完整
  coverage proof 时的落点。`ProofCheckingFixedRule37PlusData` 则允许把任意
  新的 targeted branch 继续接到这个 partial bundle 后面，作为逐步恢复完整
  `proofCodePAPR` checker 的增量接口。当前还提供命名的
  `ProofCheckingFixedRule37HilbertKData` 和
  `ProofCheckingFixedRule37HilbertKExcludedData` / `...ExcludedSData`，把
  `hilbert-K`、`excluded-middle` 和 `hilbert-S` 接到 fixed+rule37 base 之后。

Godel/ProofRuleFixedPair.agda
  proof-rule checker 的固定二元码组件。`fixedPairF expected-proof expected-formula`
  检查输入 `(proof-code, formula-code)` 是否分别等于两个固定期望码，并证明
  complete/sound；`fixedPairPR-represented` 通过 `PRRepresentabilityFinal` 得到
  PA 表示性。后续固定公理叶子和无参数固定规则分支可以复用这层。

Godel/ProofRuleFixedPairTarget.agda
  把 fixed-pair 组件包装成 rule-level target：`ProofRuleFixedPairPR`
  给出 complete/sound 接口，`proofRuleFixedPairPR` 是 canonical 实例，
  `proofRuleFixedPairPARepresentability` 把它接到最终 PR 表示性定理。

Godel/ProofRuleFixedProof.agda
  把任意已知的 `p : PA-provable A` 包装成固定 proof-checker leaf：
  proof code 是 `canonicalCodePAProof p`，formula code 是
  `canonicalNatFormula A`。该模块复用 fixed-pair target，并证明 successful
  PR check 可转回 `DecodedExecutableProofCodeNat` 和 `ExecutableProofCodeNat`。
  这覆盖 PA 的固定公理叶子，也给后续固定 derived proof leaf 复用。

Godel/ProofRuleFixedProofOr.agda
  固定 proof leaf 的二元 OR 组合器。`fixedProofOrPR p q` 把两个固定
  proof-checker leaves 合成一个 `PRRel 2`，并证明 complete/sound、到
  decoded/executable proof target 的 adapter，以及通过 `PRRepresentabilityFinal`
  得到 PA 表示性。后续聚合 PA 的多个固定公理叶子时，应先给具体 expected
  codes 建 named/opaque boundary，再用这层组合，避免 Agda 展开巨大公式码。

Godel/ProofRuleFixedCodeLeaf.agda
  explicit expected-code 版本的固定 proof leaf boundary。调用者直接给出
  `expected-proof-code`、`expected-formula-code` 和该 exact pair 的
  `DecodedExecutableProofCodeNat` witness；模块构造 `fixedCodeLeafPR`，
  证明 complete/sound、decoded/executable adapters，并提供二元
  `fixedCodeLeafOrPR` 组合器。这个接口是后续聚合多个 PA 固定公理叶子的推荐
  路径，因为它不会在 OR 树里重新展开大型 canonical formula code。

Godel/ProofRulePAAxiomLeaves.agda
  PA 六个无参数公理的 named fixed-code leaves：
  suc-not-zero、suc-injective、add-zero、add-suc、mul-zero、mul-suc。每个 leaf
  都已经通过 `fixedCodeLeafPR-represented` 接到 `PRRepresentabilityFinal`，并保留
  exact decoded checker witness。induction schema 因为携带公式参数，单独放在
  `ProofRulePAAxiomInduction` 的 target 层。多 leaf OR 聚合暂不在这里展开；它需要更细的 opaque-code
  boundary，以免一次性规约多个大型 formula code。

Godel/ProofRulePAAxiomInduction.agda
  parameterized PA induction axiom 的 target 层。它覆盖 proof-rule tag 0 下
  `checkPAAxiomCode` 的 induction schema 子分支：proof code 形如
  `node 0 (node 6 (A-code) :: [])`，输出公式为
  `canonicalNatFormula (induction A)`，并给出 decoded checker adapter。

Godel/ProofRulePRDisjunction.agda
  proof-rule `PRRel 2` 的通用二元 OR 组合器。`orProofRulePR left right`
  只在 relation 层组合两个 checker branch，并通过 `PRRepresentabilityFinal`
  得到 PA 表示性；soundness 只暴露 branch 非零信息，避免强行特化大型
  decoded adapters。

Godel/ProofRulePAAxiomPairs.agda
  用 fixed-code leaves 和 generic OR relation 组合出 PA 六个无参数固定公理的
  aggregate checker branch：`paFixedAxiomLeafPR`。该 relation 已通过
  `paFixedAxiomLeafPR-represented` 接到最终 PR 表示性定理。decoded/executable
  adapters 仍保持在 generic leaf/or 层，等后续 opaque-code 边界更细后再安全
  特化。

Godel/ProofRuleHilbertK.agda
  proof-rule tag 1 (`hilbert-K`) 的语义 target 和 proof-checker branch
  边界。`HilbertKRuleNat` 描述 canonical proof code
  `node 1 (A-code , B-code)` 与输出公式 code
  `canonicalNatFormula (A ⇒ B ⇒ A)` 的关系，并给出到
  `DecodedExecutableProofCodeNat` 的 adapter。`ProofRuleHilbertKCheckingBranchData`
  记录未来 concrete PR checker 进入 OR tree 所需的 nonzero soundness。

Godel/ProofRuleHilbertS.agda
  proof-rule tag 2 (`hilbert-S`) 的语义 target 和 proof-checker branch 边界。
  `HilbertSRuleNat` 描述 canonical proof code
  `node 2 (A-code , B-code , C-code)` 与输出公式 code
  `canonicalNatFormula ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)` 的关系，并给出到
  `DecodedExecutableProofCodeNat` 的 adapter。

Godel/ProofRuleExcludedMiddle.agda
  proof-rule tag 3 (`excluded-middle`) 的语义 target 和 branch 边界。
  `ExcludedMiddleRuleNat` 描述 canonical proof code `node 3 (A-code)` 与
  输出公式 code `canonicalNatFormula (A ∨ ¬A)` 的关系，并给出到
  `DecodedExecutableProofCodeNat` 的 adapter。

Godel/ProofRuleRecursiveSchemas.agda
  recursive proof-tree rules 的 target 层。当前覆盖 tag 4 (`modus-ponens`)
  和 tag 5 (`forall-generalize`)：targets 使用子 proof-code 的
  `checkPAProofCode` 语义描述 checker 的递归调用，并给出到
  `DecodedExecutableProofCodeNat` 的 adapter。这是后续 concrete recursive
  PR checker 要实现的规格边界。

Godel/ProofCheckingRecursiveBundle.agda
  tag 4/5 的参数化 OR bundle。它把 recursive proof-tree targets 组合成
  `RecursiveTarget₂`，并已接入当前 `ProofCheckingTargetOverview`。

Godel/ProofRuleEqRefl.agda
  proof-rule tag 8 (`eq-refl-rule`) 的语义 target 和 branch 边界。
  `EqReflRuleNat` 描述 canonical proof code `node 8 (term-code)` 与输出公式
  code `canonicalNatFormula (t ≈ t)` 的关系，是 proof checker target 分解中
  第一条 term-decoder 风格的分支。

Godel/ProofRuleEqualitySchemas.agda
  equality schema proof rules 的 target 层。当前包含 tag 9 (`eq-sym-rule`)
  到 tag 13 (`mul-cong-rule`)：定义 `EqSymRuleNat`、`EqTransRuleNat`、
  `SucCongRuleNat`、`AddCongRuleNat`、`MulCongRuleNat`，给出到
  `DecodedExecutableProofCodeNat` 的 adapter，并暴露未来 concrete PR branch
  所需的 checking-branch records。

Godel/ProofCheckingEqualityBundle.agda
  equality-related proof-rule targets 的参数化 OR bundle。它把 tag 8
  (`eq-refl`) 到 tag 13 (`mul-cong`) 的 targeted branches 组合成
  `EqualityTarget₆`，方便后续作为一个 extra branch 接到主 `proofCodePAPR`
  OR tree。

Godel/ProofRuleEqualitySubstitution.agda
  equality substitution/value proof rules 的 target 层。当前覆盖 tag 24
  (`eq-unique-value`)、tag 35 (`eq-subst-right`) 和 tag 36
  (`eq-subst-suc-right`)：定义对应 semantic targets，给出 decoded checker
  adapters，并暴露未来 concrete PR branch 所需的 checking-branch records。

Godel/ProofCheckingEqualitySubstitutionBundle.agda
  tag 24/35/36 的参数化 OR bundle。它把 equality-substitution targets 组合成
  `EqualitySubstitutionTarget₃`，并已接入当前 `ProofCheckingTargetOverview`。

Godel/ProofRuleDerivedLogicalSchemas.agda
  derived logical helper proof rules 的 target 层。当前覆盖 tag 25-34 和
  tag 38：包括 and-left/right implication helpers、imp-and-intro2、
  and-map helpers、body-unique-compose 和 contradiction-to-neg，并给出 decoded
  checker adapters。

Godel/ProofCheckingDerivedLogicalBundle.agda
  tag 25-34/38 的参数化 OR bundle。它把这些 derived logical targets 组合成
  `DerivedLogicalTarget₁₁`，并已接入当前 `ProofCheckingTargetOverview`。

Godel/ProofRuleLogicalConnectives.agda
  logical connective proof rules 的 target 层。当前覆盖 tag 19 (`and-introduce`)
  到 tag 23 (`or-intro-right`)：定义对应的 `AndIntroRuleNat`、
  `AndElimLeftRuleNat`、`AndElimRightRuleNat`、`OrIntroLeftRuleNat`、
  `OrIntroRightRuleNat`，并给出到 `DecodedExecutableProofCodeNat` 的 adapter。

Godel/ProofCheckingLogicalBundle.agda
  logical connective targets 的参数化 OR bundle。它把 tag 19-23 的 targeted
  branches 组合成 `LogicalTarget₅`，可作为后续主 proof checker OR tree 的
  一个 extra branch。

Godel/ProofRuleSubstitutionSchemas.agda
  formula/term substitution-style proof rules 的 target 层。当前覆盖 tag 6
  (`forall-eliminate`) 和 tag 7 (`exists-introduce`)：定义
  `ForallEliminateRuleNat`、`ExistsIntroduceRuleNat`，并给出 decoded checker
  adapters。

Godel/ProofCheckingSubstitutionBundle.agda
  tag 6/7 的参数化 OR bundle。它把 substitution targets 组合成
  `SubstitutionTarget₂`，并已接入当前 `ProofCheckingTargetOverview`。

Godel/ProofRuleQuantifierSchemas.agda
  quantifier / existential-prefix proof rules 的 target 层。当前覆盖 tag 14
  (`exists-eliminate`) 到 tag 18 (`premise-change-any`)：定义对应的
  `ExistsElimRuleNat`、`ExistsPrefixIntroduceRuleNat`、
  `ExistsPrefixBinaryLiftRuleNat`、`ExistsPrefixPremiseMapRuleNat`、
  `PremiseChangeRuleNat`，并给出 decoded checker adapters。

Godel/ProofCheckingQuantifierBundle.agda
  tag 14-18 的参数化 OR bundle。它把 quantifier/existential-prefix targets
  组合成 `QuantifierTarget₅`，可作为后续主 proof checker OR tree 的一个
  extra branch。

Godel/ProofCheckingTargetOverview.agda
  当前 proof checker target slice 的总览接口。它把 fixed PA axiom leaves、
  parameterized induction axiom、rule37、Hilbert K/S、excluded middle、
  recursive proof-tree rules、substitution-style rules、equality/congruence、
  equality-substitution/value、derived logical helpers、quantifier schemas 和
  logical connective branches 聚合成
  `CurrentProofCheckingTarget`，并在调用方给出 decoded coverage proof 时导出
  `ProofCheckingPRDecodedNat` 或 theorem-facing `ProofCheckingPR`。

Godel/ProofCheckingTargetCoverage.agda
  decoded coverage proof 的起点。它提供参数化的
  `CurrentProofCheckingTarget` 注入 helpers，并加入 canonical decoder no-junk
  lemmas 后的 branch coverage：Hilbert K/S、excluded-middle、PA induction
  axiom、forall/exists substitution、logical connective rules，以及
  equality/congruence、equality-substitution/value、derived logical helper
  rules 和 quantifier/existential prefix rules。模块保持对 fixed PA axiom
  leaves 参数化，避免 coverage 证明阶段强制展开大型 concrete axiom codes。

Godel/ProofRuleTargets.agda
  proof-step checker 的单规则 target 层。当前已拆出 rule 37：
  `ClosedNumeralNeqRuleNat`，即 closed numeral inequality 规则；并证明该
  rule target 可以转回 `DecodedExecutableProofCodeNat`。同时提供
  closed proof-code builder `closedNumeralNeqProofCodeF`，证明它计算出
  canonical rule-37 proof code；还接入了
  `closedNumeralNeqFormulaCodeF`，证明它计算出 expected formula code。二者都
  通过 `PRRepresentabilityFinal.prf-represented` 得到 PA 表示性。现在还新增了
  `rule37ChildrenCodePR`，检查 children-code 是否正是 `[atom m, atom n]` 的
  canonical list code；它已有 sound/complete 和 PA representability，是把
  rule37 proof-code branch 从 monolithic equality 拆成 node parser + payload
  checker 的中间层。

Godel/ProofRule37NodeChildren.agda
  rule37 proof-code branch 的轻量 concrete step。它组合
  `CanonicalCodeRawNodePR.rawNodeCodePR` 和
  `ProofRuleTargets.rule37ChildrenCodePR`，得到
  `rule37NodeChildrenPR`：检查 `(proof-code, children-code, m, n)` 满足
  proof-code 是 tag 37 的 raw node，且 children-code 正是
  `[atom m, atom n]`。该 relation 已有 sound/complete、canonical complete
  和 PA representability；下一步可以在它之上接 formula-code 与 `m ≠ n`
  分支，而不重新展开 monolithic proof-code equality。

Godel/ProofRule37DecomposedWitness.agda
  rule37 的五元拆分 witness branch，输入
  `(m,n,proof-code,children-code,formula-code)`。它用
  `rule37NodeChildrenPR` 检查 proof-code 外壳和 children payload，再组合已有
  formula-code branch 与 `m ≠ n` branch，导出
  `rule37DecomposedWitnessPR` 的 sound/complete、canonical witness 入口和 PA
  representability。这个分支是把旧 `rule37WitnessPR` 的 monolithic
  proof-code equality 换成 parser-backed proof-code branch 的下一块积木；bounded
  search 的 nonzero-hit soundness 仍留给后续模块。

Godel/ProofRule37ParserWitness.agda
  parser-backed 的四元 rule37 witness wrapper。它保持搜索需要的参数形状
  `(m,n,proof-code,formula-code)`，但先用 `nodeChildrenF proof-code` 抽出
  children-code，再调用 `rule37DecomposedWitnessF`。因此
  `rule37ParserWitnessPR` 已有 sound/complete 和 PA representability，同时不再
  直接比较 proof-code 与完整 canonical proof-code。canonical completeness 和
  bounded-search nonzero-hit bridge 仍需在后续 opaque boundary 中补上。

Godel/ProofRule37SearchSkeleton.agda
  rule37 二维 bounded search 的 generic skeleton。给任意四元 hit PRF `hitF`
  生成 search PRF，并证明该 search PRF 与对应 meta-level search 对齐。这个
  skeleton 让 parser-backed search 的语义证明不需要展开
  `rule37ParserWitnessF`。

Godel/ProofRule37ParserSearch.agda
  parser-backed 的 bounded-search candidate。它平行于旧
  `ProofRule37Search.rule37SearchF`，但搜索谓词改为
  `rule37ParserWitnessF`。当前模块导出 `rule37ParserSearchF`、
  `rule37ParserSearchPR`、meta-level search mirror，以及
  已由 generic skeleton 构造的 `rule37ParserSearchSemantics`。
  `Rule37ParserSearchCorrect` 由后续 parser complete/sound 模块具体构造；
  PA adapter 暂不在这里展开，以避免重新触发大型 witness normalization。

Godel/ProofRule37ParserSearchHit.agda
  parser-backed search 的 hit-interface 桥。给定
  `Rule37ParserSearchSemantics`，它把 bounded hit/nonzero hit 转成
  `rule37ParserSearchF` 的 complete/sound，并提供
  `rule37ParserSearchHitInterface`，该 interface 与
  `rule37ParserSearchMMeta` definitionally 对齐。剩余工作现在被压缩成：
  把 `Rule37ParserWitnessExists` 与 bounded hit/nonzero hit 互相连接。

Godel/ProofRule37ParserBounds.agda
  parser-backed search 的 boundedness bridge。旧 `ProofRule37Bounds` 只处理
  proof-code 恰好等于 canonical closed rule37 code 的情况；parser 路线需要从
  raw node parser 和 children payload 推出 `m,n ≤ proof-code`。该模块证明
  `nodeChildrenF proof-code ≤ proof-code`，再结合 children-code 是
  `[atom m, atom n]` 的事实，导出 `rule37ParserWitness-bounds` 和
  `rule37ParserWitnessBoundsBridge`。

Godel/ProofRule37ParserSearchComplete.agda
  parser-backed search 的 complete bridge。它把
  `Rule37ParserWitnessExists proof-code formula-code` 转成 bounded hit：
  witnesses 本身给出 `m,n`，`ProofRule37ParserBounds` 给出搜索界，
  `rule37ParserWitness-complete` 给出 hit predicate 为 `1`。

Godel/ProofRule37ParserSearchSound.agda
  parser-backed search 的 direct sound bridge。它避免复用 generic hit-record
  projection，改为直接证明 `rule37ParserSearchF = 1` 会给出 bounded nonzero
  parser hit，再用抽象的 `rule37ParserWitness-nonzero-sound` 得到
  `Rule37ParserWitnessExists`。这样 sound half 可以 typecheck，而不会在 generic
  hit 模块中展开完整 parser witness checker。

Godel/ProofRule37ParserSearchCorrect.agda
  将 parser-backed search 的 complete/sound 收口成 concrete
  `rule37ParserSearchCorrect : Rule37ParserSearchCorrect`。这仍弱于最终
  `ProofRule37PR`：parser witness 目前只证明 raw node parser 与 payload
  facts，还没有桥回 `ClosedNumeralNeqRuleNat` 的 canonical proof-code equality。

Godel/ProofRule37CanonicalBridge.agda
  证明 full canonical parser target 可以桥回旧的 rule37 语义目标。模块先用
  `parseCodeList-canonical` 证明 `encodeCodeListWithRest _ zero` 的注入性，
  再证明：如果 outer node 是 canonical `NodeCodeNat proof-code 37
  children-code`，且 children-code 是 `[atom m, atom n]`，那么
  `proof-code ≡ closedNumeralNeqCode m n`。因此
  `Rule37CanonicalParserWitnessNat` 可以推出 `ClosedNumeralNeqRuleNat`。这说明
  下一步不是继续强化 raw parser，而是把 rule37 PR branch 升级到 full
  canonical node/list parser target。

Godel/ProofRule37CanonicalWitness.agda
  将 full canonical parser witness 封装成 search-facing 目标
  `Rule37CanonicalWitnessExists`，并证明它与 `ClosedNumeralNeqRuleNat` 双向
  对应：`closedRule37-to-canonicalWitness` 和
  `canonicalWitness-to-closedRule37`。模块还定义
  `ProofRule37CanonicalWitnessSearchPR`：只要后续给出一个 PR relation 精确刻画
  canonical witness search，就能通过
  `proofRule37PR-from-canonical-witness-search` 得到最终 `ProofRule37PR`，并通过
  `proofRule37CanonicalWitnessSearchPR-represented` 接到
  `PRRepresentabilityFinal`。

  另外新增了 witness-carrying checker `rule37WitnessPR`，输入
  `(m,n,proof-code,formula-code)` 并组合 proof-code、formula-code 与 `m ≠ n`
  三个条件。该 checker 已拆出 branch-level correctness、branch-level
  sound/complete、raw `andF` sound/complete，并证明整体 witness checker 的
  evaluator-level complete；`rule37WitnessF-sound-ones` 还可从整体 checker
  为 `1` 推出三个 branch 都为 `1`；`rule37WitnessF-sound` 已把这三个
  branch facts 合成为 `Rule37WitnessNat`。`rule37WitnessPR-represented` 已经
  通过 `PRRepresentabilityFinal.prrel-represented` 得到 PA 表示性。
  `ProofRule37PR` 和通过
  `PRRepresentabilityFinal.prrel-represented` 的 PA 表示性 adapter 仍是后续完整
  rule relation 的接口。

Godel/ProofRule37CanonicalSearch.agda
  将 Lean shadow 里建议的 canonical witness search 分层落实为 Agda
  boundary。它定义 bounded canonical witness 目标
  `Rule37CanonicalBoundedWitnessExists`，并证明任意 canonical parser witness
  都能给出 `m,n ≤ proof-code` 的 search bounds。模块现在还实现了
  `rule37CanonicalWitnessF` 和 `rule37CanonicalSearchF`：给定一个 full
  `CanonicalCodeNodeParserPR` 以及它的 nonzero soundness，就能导出
  `proofRule37CanonicalBoundedSearchPR-from-node-parser` 和
  `proofRule37CanonicalCheckingBranchData-from-node-parser`。也就是说，
  rule37 的 bounded canonical witness search 本身已经接好；full
  `NodeCodeNat` parser 现在可由 code-list-length parser 派生，剩余缺口被
  进一步缩到 `code-list-length-pr` 的 concrete PR 实例及其 nonzero-sound。

Godel/ProofRule37FromCodeListLength.agda
  将剩余的 code-list-length parser obligation 接到 rule37 分支的最终入口：
  给定 `CanonicalCodeParserPR` 和 `CodeListLengthNonzeroSound`，它先构造
  `CanonicalCodeNodeParserSearchData`，再导出
  `ProofRule37CheckingBranchData`。因此从 list-length parser 到 rule37
  `proofCodePAPR` branch 的接线已经闭合；下一步只剩把 list-length parser
  本身 concrete 化。

Godel/ProofRule37PRHolds.agda
  rule37 witness checker 的轻量 `PRRel-holds` adapter。直接在
  `PRRel-holds rule37WitnessPR ...` 目标里展开 `rule37WitnessPR` 会触发过重
  normalization；该模块先证明 inline relation `(rel rule37WitnessF)` 的
  complete/sound，再通过 `rule37WitnessPR ≡ rel rule37WitnessF` 的 `subst`
  adapter 得到 named `rule37WitnessPR` 的 complete/sound。还定义
  `Rule37WitnessExists proof-code formula-code`，表示存在 witness `m,n` 通过
  `rule37WitnessPR`，并证明它与 `ClosedNumeralNeqRuleNat` 双向对应；这就是后续
  把 witness search 收缩成真正二元 `PRRel 2` 的规格边界。进一步新增
  `ProofRule37WitnessSearchPR`：任何二元 PR relation 只要精确刻画
  `Rule37WitnessExists`，就能通过 `proofRule37PR-from-witness-search` 生成
  `ProofRule37PR`，并由 `proofRule37WitnessSearchPR-represented` 接到
  `PRRepresentabilityFinal`。

Godel/ProofRule37Bounds.agda
  rule37 bounded search 的纯编码界证明。它不展开 witness checker，只证明
  canonical proof code `closedNumeralNeqCode m n` 中携带的两个 witness
  `m,n` 都满足 `m ≤ closedNumeralNeqCode m n` 和
  `n ≤ closedNumeralNeqCode m n`；并给出通过
  `proof-code ≡ closedNumeralNeqCode m n` 传递到任意 `proof-code` 的版本。
  这是把 `Rule37WitnessExists` 接到 bounded search completeness 的独立前置。

Godel/ProofRule37Search.agda
  rule37 的 concrete bounded-search PRF candidate。它定义
  `rule37SearchF : PRF 2`，用 `proof-code` 作为 bound，搜索所有
  `m,n ≤ proof-code` 并调用四参数 `rule37WitnessF`。模块还证明
  `rule37SearchF-correct`：该 PRF 的 `evalPRF` 等于干净的 meta-level
  bounded search。`Rule37SearchCorrect` 精确记录下一步还要证明的内容：
  该 bounded search 与 `Rule37WitnessExists` 双向对应；一旦给出这个证明，
  `proofRule37WitnessSearchPR-from-search-correct` 就生成
  `ProofRule37WitnessSearchPR`。

Godel/ProofRule37SearchCorrectness.agda
  rule37 bounded search 使用的 generic meta-level search 语义引理。当前已证明
  任意谓词 `P : ℕ → ℕ` 如果在某个 `n ≤ bound` 处返回 `1`，则
  `searchUpTo P bound` 返回 `1`；同时证明了二维 nested bounded search 的
  对应命中定理。反方向也已有 generic soundness：如果一维或二维 search
  返回 `1`，则存在一个有界位置，其谓词值非零。该模块刻意不直接实例化大型
  `rule37WitnessF`，以避免 proof checker route 中的重归约；下一步会通过
  一个小的 witness-hit 封装把这些 generic lemmas 接到 rule37 search。

Godel/ProofRule37SearchHit.agda
  rule37 search completeness 的薄接口层。`Rule37SearchHitInterface` 把
  “用于 bounded search 的 hit predicate” 和真实 `rule37SearchMMeta` 的对齐
  分开记录；`Rule37WitnessHitBridge` 再把外部 witness specification 接到
  bounded hit。给出该 bridge 后，`rule37Search-complete-from-hit-bridge`
  可推出 `rule37SearchF` 的 completeness，而不在 search proof 中展开大型
  `rule37WitnessF`。同时提供对称的 `Rule37WitnessHitSoundBridge`：只要能把
  bounded nonzero hit 转回目标 witness specification，就能通过
  `rule37Search-sound-from-hit-bridge` 推出 search soundness。现在还导出
  `rule37Search-sound-bounded-nonzero` 和
  `rule37Search-nonzero-sound-from-hit-bridge`，用于最终 proof-checker OR 树需要
  的 nonzero-hit soundness。

Godel/ProofRule37SemanticHit.agda
  将 rule37 的语义 target 接到 bounded-hit 形状。给定一个
  `Rule37SearchHitInterface` 和一个很窄的 `Rule37SemanticHitComplete`
  字段（`Rule37WitnessNat` 让该 hit predicate 返回 `1`），模块用
  `ProofRule37Bounds` 自动把 `ClosedNumeralNeqRuleNat` 转成
  `Rule37WitnessBoundedHit`，并导出 `rule37Search-complete-closedRule37`。
  因此 rule37 search completeness 的剩余缺口被缩小为：实例化 hit predicate
  与大型 `rule37WitnessF` 的成功条件一致。

Godel/ProofRule37ActualHit.agda
  实例化 `Rule37SearchHitInterface` 的 hit predicate 为真实的
  `rule37WitnessValue`，并证明它与 `rule37SearchMMeta` definitionally 对齐。
  模块导出 `Rule37ActualHitData`：只剩一个字段要求证明
  `Rule37WitnessNat → rule37WitnessValue = 1`。给出这个字段后，
  `rule37Search-complete-closedRule37-actual` 会得到 rule37 search 对
  `ClosedNumeralNeqRuleNat` 的 completeness。

Godel/ProofRule37ActualSearch.agda
  将 actual hit completeness 和 actual hit soundness bridge 聚合成
  `Rule37ActualSearchData`，并导出 `proofRule37PR-from-actual-search`。也就是说，
  rule37 的 concrete `rule37SearchPR` 已经能在该数据下生成完整
  `ProofRule37PR`；其中 completeness 由前面模块组合得到，soundness 通过
  `Rule37WitnessHitSoundBridge ClosedNumeralNeqRuleNat` 表达。现在还导出
  `rule37Search-nonzero-sound-actual` 和
  `proofRule37CheckingBranchData-from-actual-search`，所以 actual search data
  可以直接进入 `ProofCheckingRule37Branch` 的 targeted proof-checker branch。

Godel/ProofRule37ArgsHit.agda
  记录 args-based hit route 的剩余义务。该 route 用
  `rule37WitnessArgs` 直接定义 `rule37ArgsHitValue`，因此后续证明应能复用
  `ProofRuleTargets` 中已有的 witness checker complete/sound theorem。当前模块
  将 search meta alignment、search completeness、search soundness 作为
  `Rule37ArgsSearchData` 字段，并给出到 `ProofRule37PR` 的 adapter。现在还提供
  `Rule37ArgsCheckingBranchData`：只要额外给出 nonzero soundness，就能导出
  `ProofRule37CheckingBranchData` 并进入 proof checker OR tree。

Godel/PRBooleanSoundness.agda
  proof checker route 的小型布尔语义工具。当前提供 opaque 的
  `and-output-sound`，用于从 `output = left * right` 与 `output = 1` 推出
  两个 branch 都为 `1`，避免 rule-level sound proof 直接展开大型
  `evalPRF` branch。

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
   `evaluatedGraphFormula`。primitive recursion 现在另有 structured
   PA-history 公式入口，显式包含 ∃s、sequence length、history-valid、nth
   约束；新的 `structured-primitive-recursion-closes` 已不再使用 evaluated
   graph 左支撑。`PRStructuredTheorem` 将它汇总为推荐的
   `prf-represented` / `prrel-represented`。旧 history-backed closure 和旧
   PRRepresentability implementation 仍保留为兼容 bridge。historyCode 已改成可
   round-trip 的 canonical nat-list 编码；seqLengthF/seqNthF 已有最小基 PRF
   候选，并已有 evalPRF-to-meta 的语义镜像证明。seqLength/seqNth 都已证明
   与 historyLength/historyNthDefault 一致，因此现在可以无条件导出
   `concretePRSequenceCoding`。`history-validF` 现在也已实现为最小基 bounded
   step checker，并证明真实 evalHistory 会被接受。第二步已经通过
   `PRRepresentabilityFinal` 收口。当前新加入的 `ProofCanonicalCoding`、
   `ProofCanonicalChecker` 和 `ProofCheckingPR` 是下一大阶段的入口：
   canonical proof-tree 数值编码、round-trip、executable checker 和 complete
   / PA-provable-sound 方向已经就位；下一步是把 executable checker 展开成
   PR relation。当前已新增 decoded executable 语义，后续 PRF 展开可以对准
   “numeric decode + code-level proof-step checker” 这个分解形状，并最终把
   canonical checker 接回旧 `ProofCodePA` / `ProofOf`。`ProofCheckingPRTargets`
   现在给出了这个全数值目标和到 `ProofCheckingPR` 的 adapter。
   `CanonicalCodeRawNodePR` 已经给出 proof-rule dispatch 需要的 raw outer
   node concrete PR branch；`CanonicalCodeRawListPR` 已经给出 code-list
   nil/cons 的 raw branch；`CanonicalCodeRawAtomListPR` 已经给出 atom-head
   cons payload 的 concrete PR branch；`ProofRuleTargets.rule37ChildrenCodePR`
   已经给出 rule37 children payload `[atom m, atom n]` 的 represented PR
   checker；`ProofCheckingPRComponents` 已经落下第一个 concrete PR piece：
   公式码相等。

在本工程中，这两个部分以 record 字段给出：

```agda
record PARepresentability : Set₁ where ...
record DiagonalLemma (T : ArithmetizedTheory) : Set where ...
```

只要补齐这两个 record 的实例，`PA-first-incompleteness` 就直接给出 PA 的第一不完备性结论。
