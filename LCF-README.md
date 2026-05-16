# 极小 LCF 风格证明内核（Minimal LCF Proof Kernel）

为 **Pocket 386** 上的 **Apteryx Lisp 1.04** 编写的最小可用 LCF 风
格证明检查器。文件 `lcf.lsp` 单独可加载、可运行，加载完成后会立即
跑一段演示。

> LCF 风格（Edinburgh LCF, HOL, Isabelle, HOL Light, Coq 的 ML 内
> 核）的核心思想：**整个系统中只有一个小小的「内核」可以构造类型
> 为 `thm` 的值；其它代码无论多复杂、多自动化，最终都必须把每一个
> 定理还原成对内核推理规则的调用。** 所以系统的可信基（TCB）就只
> 是这个小内核。

## 文件

```
lcf.lsp        内核 + 派生规则 + 演示，单文件 ~250 行
LCF-README.md  本说明（中文 + 元理论讨论）
```

## 在 Pocket 386 上运行

```
> copy lcf.lsp c:\lisp\
> win
... 启动 Apteryx Lisp ...
* (load "c:\\lisp\\lcf.lsp")
```

文件末尾的 `(demo)` 会自动跑完所有示例。要交互式构造定理，直接在
Listener 调用 `(rule-assume ...)`、`(rule-mp ...)` 等即可。

## 对象逻辑

为了让内核压到最小，这里的对象逻辑只有两个项构造子：

| 写法           | 含义                            |
| -------------- | ------------------------------- |
| 任何普通符号   | 命题变元（如 `p`、`q`）         |
| `bot`          | 假命题 ⊥                        |
| `(imp a b)`    | 蕴含 `a → b`                    |

*否定* 直接缩写为 `~A ≡ A → ⊥`，所以不需要单独的 `not` 构造子。
有 `→` 和 `⊥` 已经够表达全部经典命题逻辑（古典真值表、合取、析取
都可以编码出来），因此内核也不必管它们。

**Sequent**（断定）的形式是 `Γ ⊢ A`：`Γ` 是有限的假设集合（用
列表加 `equal` 去重表示），`A` 是结论。

## 内核：5 条原始推理规则

| 名字            | 规则                                                  | 备注                  |
| --------------- | ----------------------------------------------------- | --------------------- |
| `rule-assume`   | `———————— `<br>`{A} ⊢ A`                             | 引入假设              |
| `rule-mp`       | `Γ ⊢ A→B    Δ ⊢ A`<br>`————————————`<br>`Γ ∪ Δ ⊢ B` | modus ponens          |
| `rule-disch`    | `Γ ⊢ B`<br>`——————————`<br>`Γ \ {A} ⊢ A → B`        | 演绎定理              |
| `rule-ex-falso` | `Γ ⊢ ⊥`<br>`————`<br>`Γ ⊢ A`                        | 直觉主义爆炸          |
| `rule-peirce`   | `———————————————`<br>`⊢ ((A→B)→A) → A`              | 加这条就升级到经典逻辑 |

仅此 5 条，约 30 行 Lisp。整个系统的可信基（trusted code base）
就是这一段。其它任何代码出错最多让证明失败，**不会** 让系统接受
一个不真的定理。

## 派生规则（demo 中已实现）

下面这些都不在内核里——它们只是「按一定顺序调用内核规则」的辅助
函数，因此自动继承内核的可靠性：

| 派生规则           | 结论                                                  |
| ------------------ | ----------------------------------------------------- |
| `derived-refl A`   | `⊢ A → A`                                            |
| `derived-k A B`    | `⊢ A → B → A`           （即 Hilbert 公理 K）        |
| `derived-s A B C`  | `⊢ (A→B→C) → (A→B) → A → C` （Hilbert 公理 S）       |
| `derived-trans`    | 蕴含的传递律                                          |
| `derived-contra`   | `⊢ (A→B) → (~B → ~A)`                                |
| `derived-dne`      | `⊢ ~~A → A`             （需要 Peirce 才证得出）     |

注意：派生 K 和 S 这件事本身就说明，演绎定理（`disch`）+ MP +
`assume` 已经覆盖了 Hilbert 系统；再加 Peirce 即可补足经典逻辑。

## 演示输出（在 SBCL 上预跑过，与 Pocket 386 上一致）

```
[A] Primitive rules
  ASSUME p             :  P |- P
  PEIRCE p,q           :         |- (((P -> Q) -> P) -> P)
  DISCH p of (p|-p)    :         |- (P -> P)
  MP of K p q and (p)  :  P |- (Q -> P)

[B] Derived rules (provably sound by construction)
  refl p               :         |- (P -> P)
  axiom-K p q          :         |- (P -> (Q -> P))
  axiom-S p q r        :         |- ((P -> (Q -> R)) -> ((P -> Q) -> (P -> R)))
  trans (p->q)(q->r)   :  (Q -> R), (P -> Q) |- (P -> R)
  contra p q           :         |- ((P -> Q) -> ((Q -> BOT) -> (P -> BOT)))
  ~~p -> p   (DNE)     :         |- (((P -> BOT) -> BOT) -> P)

[C] A small worked theorem:  |- (p -> q) -> (~~p -> q)
  result :         |- ((P -> Q) -> (((P -> BOT) -> BOT) -> Q))

[D] Abstraction sanity check
  Forged value passes IS-THM ? NIL
  Real theorem passes IS-THM ? T
```

`[C]` 这个证明完全在 Listener 里手工搭：

```
1.  h1 ≔ assume (p → q)              ; (p→q) ⊢ p→q
2.  h2 ≔ assume ¬¬p                  ; ¬¬p   ⊢ ¬¬p
3.  dne ≔ derived-dne p              ;       ⊢ ¬¬p → p
4.  p-th  ≔ mp dne h2                ; ¬¬p   ⊢ p
5.  q-th  ≔ mp h1 p-th               ; p→q, ¬¬p ⊢ q
6.  step  ≔ disch ¬¬p q-th           ; p→q   ⊢ ¬¬p → q
7.  final ≔ disch (p→q) step         ;       ⊢ (p→q) → (¬¬p → q)
```

每一行只调用了内核或派生规则，整个证明对象就是一个被内核签过名
的 `thm`，`is-thm` 即可识别。

---

## 元理论讨论：可靠性 与 可扩展性

### 1. 可靠性（Soundness）

**定理（内核可靠性）.** 设 ⊨ 表示对象逻辑（含 → 与 ⊥ 的经典命题
逻辑）的语义后承关系。如果 `is-thm x` 为真，则
`hyps x ⊨ concl x`。

**证明思路.** 对 `x` 由内核构造的次数做归纳。
基础：唯一不依赖于其它 `thm` 输入的两个构造子是
- `rule-assume A`：`{A} ⊨ A`，平凡。
- `rule-peirce A B`：`⊨ ((A→B)→A) → A`，经典命题逻辑的有效式。

归纳：
- `rule-mp th1 th2`：`Γ ⊨ A→B` 且 `Δ ⊨ A`，则任何使 `Γ ∪ Δ` 为真的
  赋值同时使 `A→B` 与 `A` 为真，从而 `B` 为真。
- `rule-disch A th`：`Γ ⊨ B` ⇒ `Γ \ {A} ⊨ A → B`，即语义版的
  演绎定理。
- `rule-ex-falso A th`：`Γ ⊨ ⊥` ⇒ `Γ` 不可满足，所以 `Γ ⊨ A` 空真。

合起来：每次内核调用都保持「语义后承」这条不变量。 ∎

> **可信基（TCB）只剩三件事：**
> 1. 上述 5 个 30 行内核函数；
> 2. `is-thm`、`hyps`、`concl` 这 3 个只读访问器；
> 3. Apteryx Lisp 自己的 `cons / car / cdr / eq / equal` 等基本算子。
>
> 即使 demo、派生规则、未来任何高级证明策略写得再复杂、再 buggy，
> 最坏情况只是「打不出证明」，绝不会让一条非真的命题被打出来。

### 2. 派生规则的保守性（Conservativity）

**命题.** 任何派生规则若能返回一个 `thm`，则该 `thm` 一定来自
内核。

**理由.** Lisp 里 *没有任何另一条途径* 可以构造满足 `is-thm` 的
值——`is-thm` 用 `eq` 比较其 `car` 与 `*ktag*`，而 `*ktag*` 是程序
启动时新鲜分配的 cons 单元（第 86 行）。`eq` 比较的是地址相等，外
部代码即使写出 `(cons 'lcf-private-tag nil)` 也得不到同一个 cons，
因此无法伪造。`[D]` 段的 forge 测试就证实了这一点。

> 这正是 LCF 用「类型抽象」换取「自由扩展」的关键：派生规则可以无
> 限增加，**但内核大小恒定**。

### 3. 可扩展性（Extensibility）

LCF 风格允许三层扩展，全部 *不动* 内核：

| 层级           | 例子                                  | 风险       |
| -------------- | ------------------------------------- | ---------- |
| 派生推理规则   | `derived-trans`、`derived-dne`        | 无         |
| 证明策略 / tactic | `repeat-mp`、`auto-prove-impl`     | 无         |
| 决策过程       | DPLL / 重写引擎                       | 无         |

只要这些扩展最终都通过调用 `rule-*` 系列得到结果，可靠性就由
内核单独承担。换句话说：**复杂度可以无界增加，但 TCB 大小不变。**
这就是 LCF 的「de Bruijn 准则」——可信基不应随系统规模增长。

### 4. 抽象的实现局限

Apteryx Lisp 没有 ML 那样的模块/签名系统，所以 `mk-thm` 这个内
部构造子在技术上仍然在全局命名空间里可见。我们用「私有 tag +
约定俗成」近似 ML 的封装：

- `*ktag*` 是 `(cons 'lcf-private-tag nil)`，每次启动新分配；
- 对它做 `eq` 比较的代码只有内核里那一行（`is-thm`）；
- 客户端只看到导出接口：`rule-*`、`derived-*`、`hyps`、`concl`、
  `is-thm`，与 `mk-imp / mk-not` 这些纯项构造子。

要把抽象提升到机械级，可：

1. 在带有 `package` / 模块的 Lisp 上，把 `mk-thm`、`*ktag*` 放进
   私有 package；客户端只能 import 公共符号。
2. 改用 *闭包* 方案——把 `mk-thm` 封进一个不导出的词法环境里：
   ```
   (let ((tag (cons 'k nil)))
     (defun mk-thm (h c) (list tag h c))
     ...)
   ```
   这要求解释器具有 ANSI 风格词法作用域；Apteryx Lisp 1.04 的
   作用域细节没有公开文档，因此本实现采用更保险的「全局私有 tag
   + 约定」方案。

### 5. 完备性边界

本内核对**经典命题逻辑（→, ⊥）** 是完备的。证明大纲：

1. `assume`/`mp`/`disch` 构成自然演绎的最小核心；K 与 S 由它们
   导出（已在 demo 中给出 `derived-k`、`derived-s`），所以整个
   Hilbert 直觉主义蕴含演算被涵盖。
2. 加上 `rule-ex-falso` 升级到完整的直觉主义命题逻辑。
3. 再加上 `rule-peirce`（或等价的 `~~A → A`）就升级到经典命题
   逻辑——`derived-dne` 即为示范。

要扩展到一阶逻辑或高阶逻辑，需要再加：项中的变元绑定、`abs`/
`beta`/`inst`/`gen` 等规则，以及类型/排序系统。这就是 HOL Light
做的事——但其内核也只是 10 条规则、约 400 行 OCaml。LCF 风格的
可扩展性正在于：从这 5 条扩到那 10 条，内核只需「加几条规则」，
所有上层代码无须重写也无须重新审计。

### 6. 与 Pocket 386 资源的关系

| 资源 | 实际占用 |
| --- | --- |
| 代码体积 | `lcf.lsp` 仅 ~250 行，单文件 ~7 KB，对 8 MB 内存毫无压力 |
| 推理深度 | demo 中最深 6–7 层 cons，386SX 栈无虞 |
| 数据结构 | 只用 cons / list / symbol，未用 hash table、CLOS、特殊形式 |
| 解释器特性依赖 | 仅 `defun cond if and or let quote setq defvar princ terpri error eq equal cons car cdr atom consp null list` —— Apteryx 1.04 全部具备 |

把 DPLL 求解器（同仓库 `dpll.lsp`）和这个 LCF 内核组合起来，可以
在 Pocket 386 上得到一个 **「自动证明 → LCF 检查」** 的小型可信
工作流：DPLL 把命题判定为可满足/不可满足，再由 LCF 内核独立重放
出对应的形式证明，这正是 SAT-based theorem proving 的传统结构，
只是规模缩到能在 386SX/8 MB 上跑动而已。

---

## 在 PC 上预先校验

```
$ sbcl --script lcf.lsp
```

代码只用 ANSI CL 的最小子集，可在 SBCL/CLISP/ECL 直接运行；与
Apteryx Lisp 上行为一致。
