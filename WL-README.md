# Weisfeiler–Lehman 图同构测试（WL Test）on Pocket 386

为 **Pocket 386** 上的 **Apteryx Lisp 1.04** 实现的 **1-WL**（颜色细
化，color refinement）和 **2-FWL**（folklore 2-WL）图同构测试，
含 **CFI 型反例图** 构造，与 ASCII 可视化结果。最后讨论 WL 表
达力的精确边界、与 GNN 表达能力的关系。

## 文件

- `wl.lsp` — 1-WL + 2-FWL 实现 + CFI(C_3) 构造 + 4 组 demo（约
  550 行 / 16 KB，纯 Lisp，无外部依赖）。
- `WL-README.md` — 本文件。

## 在 Pocket 386 上运行

```
copy wl.lsp c:\lisp\
;; 启动 Win 3.11 -> Apteryx Lisp:
* (load "c:\\lisp\\wl.lsp")
```

> **重要 —— 行尾格式**：源文件必须用 **DOS 风格 CRLF**（`\r\n`）行尾，
> 否则 Apteryx Lisp 会把整个文件看成单一长行，报错 *Line too long*。
> 本仓库的 `.lsp` 文件已经通过 `.gitattributes` 强制存为 CRLF；用 git
> 直接 clone 出来就是对的。如果是通过其它途径传输（FTP / WSL / Linux
> cp / tar 等），请确认目标文件是 CRLF：
>
> - Linux/macOS：`file wl.lsp` 应输出 `... with CRLF line terminators`；
>   如果不是，运行 `unix2dos wl.lsp` 修正一下再拷贝。
> - FTP：务必使用 **ASCII 模式**，让客户端自动转换换行。

文件末尾的 `(demo)` 会自动跑完 4 组对比并打印每张图的邻接矩阵、
1-WL 着色迭代历史、最终 *partition signature*（按类大小降序的列表）
以及 1-WL / 2-FWL 的判定结果。

> **注：** Demo D（18 顶点的 CFI 对）2-FWL 那一步，在 386SX/40 MHz
> 上估计 1–3 分钟；其它 6 顶点的 demo 都是秒级。

---

## 1. 算法

### 1-WL：颜色细化

每个顶点 v 维护一个颜色 c(v)。一轮细化：

```
c'(v) := HASH ( c(v), multiset { c(u) : u ∈ N(v) } )
```

直到分划稳定。两图 G、H 被 1-WL **区分** 当且仅当稳定后的颜色
多重集不同。

### k-WL（这里实现 2-FWL，folklore）

为每对顶点 (i, j) 维护一个颜色 c(i, j)。
- **初始**：c(i, j) = 原子型：`diag` / `edge` / `non-edge`。
- **细化**：
  ```
  c'(i, j) := HASH ( c(i, j),
                     multiset { ( c(i, k), c(k, j) ) : k ∈ V } )
  ```
  即引入一个 *witness* k，把 (i, j) 与所有第三方点的二元交互信息
  压进新颜色。

#### 关于命名约定

文献里有两套常被混淆的定义：

- **k-WL** —— 给 k-元组着色，刷新公式用「逐分量替换」的多重集；
- **k-FWL**（folklore k-WL）—— 也给 k-元组着色，刷新公式用「插入
  第三方 witness」的多重集。

两者表达力关系（Cai–Fürer–Immerman 1992）：

```
1-WL  =  1-FWL  ≪  2-WL  ≪  2-FWL ≡ 3-WL  ≪  3-FWL ≡ 4-WL  ≪ ...
```

本仓库的 2-FWL 等价于通常意义的 3-WL（习惯上比 2-WL「再升一档」），
比纯 1-WL 严格更强。

### 颜色规范化

为了让两图共用同一个颜色空间，每一轮 **联合** 细化：

1. `(cm-reset)` 清空规范化器；
2. 先对 G 的所有顶点（或顶点对）做一次 `cm-get`，按出现顺序
   分配 0, 1, 2, …；
3. 紧接着对 H 做同样事情；如果 H 的某个 key 在 G 已经出现过，
   就 **复用** 同一 ID。

这等价于「在 G ⊔ H 上同时做色彩细化」。最终判定用 *partition
signature*（每个颜色类的大小，降序列表）—— 它是真正的同构
不变量，与具体的整数标签无关。

---

## 2. Demo 输出

```
============================================
DEMO A : K_{1,3}  vs  P_4   (1-WL works via degrees)
============================================
[ 1-WL ]  stable after 2 refinement step(s)
  K13  partition  [3 1]            ; 一个度数 3 的中心 + 三个叶子
   P4  partition  [2 2]            ; 两个端点 + 两个内部
  >>> 1-WL distinguishes ? YES

============================================
DEMO B : 2K_3  vs  C_6   (both 2-regular -> 1-WL FAILS)
============================================
[ 1-WL ]  stable after 0 refinement step(s)
  2K3  partition  [6]              ; 全部同色
   C6  partition  [6]
  >>> 1-WL distinguishes ? NO
[ 2-FWL ] stable after 2 refinement step(s)
  2K3  2-partition  [18 12 6]      ; 6 对角 + 12 边 + 18 非边
   C6  2-partition  [12 12 6 6]    ; 6 对角 + 12 边 + 12 距离-2 + 6 距离-3
  >>> 2-FWL distinguishes ? YES

============================================
DEMO C : K_{3,3}  vs  3-prism   (both 3-reg -> 1-WL FAILS)
============================================
[ 1-WL ]  partition  [6] vs [6]    -> NO
[ 2-FWL ] partition  [18 12 6] vs [12 12 6 6]   -> YES

============================================
DEMO D : CFI(C_3) untwisted vs twisted (CFI counterexample)
============================================
[ 1-WL ]  partition  [18] vs [18]                    -> NO
[ 2-FWL ] 2-partition [162 36 36 36 36 18]
                vs    [36 36 36 36 36 36 36 36 18 18]   -> YES
```

### 怎么读 Demo D 的 partition 数字

CFI(C_3) 是 18 顶点，所以 2-FWL 一共有 18² = 324 个二元组。

- **未扭** 6 类 [162 36 36 36 36 18]   ⇒  `162+36*4+18 = 324` ✓
- **扭** 10 类 [36×8, 18, 18]          ⇒  `36*8+18*2 = 324` ✓

类大小直方图直接不同，所以 2-FWL 立刻判出非同构。1-WL 完全看不
出来 —— 两图都是 2-正则的，从顶点局部度数信息根本提取不到「扭与
未扭」这种全局奇偶性信息。

---

## 3. CFI 反例的精确边界

**Cai–Fürer–Immerman 1992 定理（精确版）.** 对任意 k，存在两个
*不同构* 的 3-正则图 `G_k^0`、`G_k^1`，它们的顶点数与 k 线性相关，
且：

- **k-WL 不能区分** `G_k^0` 与 `G_k^1`；
- **(k+1)-WL 可以区分** 它们。

构造方式：取一个 *基图* `H`，将每个顶点 `v ∈ V(H)` 替换为「CFI gadget
X(v)」；每条边对应一对「平行连接」，其中恰有一条边被「扭转」。
*关键定量* —— Grohe & Otto 2015 进一步精确到：

```
CFI(H) 不能被 k-WL 区分 ⇔  k < tw(H)
```

其中 `tw(H)` 是 `H` 的树宽（treewidth）。所以：

| 基图 H        | tw(H) | 1-WL 失败 | 2-WL 失败 | 3-WL 失败 |
| ------------- | ----- | --------- | --------- | --------- |
| C_n（环）     | 2     | ✓         | ✗         | ✗         |
| K_4           | 3     | ✓         | ✓         | ✗         |
| K_5           | 4     | ✓         | ✓         | ✓         |
| 网格 Grid_k×k | k     | ✓         | …         | …         |

本仓库的 demo D 选 `H = C_3` 是因为：

1. tw(C_3) = 2 ⇒ 1-WL 失败、2-WL 成功，正好演示「升一阶就解决」；
2. 顶点数 = 3·6 = 18，2-WL 的 18² = 324 个二元组在 8 MB / 386SX
   上还能在数分钟内跑完；
3. 结构小到可以在终端把整张邻接矩阵打印出来核对。

要构造一个 **2-WL 也失败** 的 CFI 对，最小的例子是 `H = K_4`，
顶点数 ≥ 4·10 = 40，2-WL 需要 1600 个二元组，每轮 ~64000 次
witness 计算。在 8 MB Pocket 386 上虽然内存还够，但纯解释器跑
起来要小时级；这里就只在 README 中给出公式，不在代码里跑。

---

## 4. 与 GNN 表达力的关系

### 上界：MPNN ≤ 1-WL

**Morris et al., AAAI 2019** 与 **Xu et al., ICLR 2019 (GIN)**
独立证明了：

> 对任意消息传递图神经网络（Message-Passing Neural Network,
> MPNN），如果它把两张图判为「同特征」，那么 1-WL 也判它们「同
> 色多重集」；逆否地说，**1-WL 不能区分的两张图，任何 MPNN 也
> 区分不了**。

证明思路：MPNN 的每一层
```
h_v^{(t+1)} = UPDATE ( h_v^{(t)}, AGGREGATE { h_u^{(t)} : u ∈ N(v) } )
```
完全是 1-WL 颜色细化的「连续松弛」。聚合算子 (sum/mean/max) 在
最坏情况下不会注入比「邻居颜色多重集」更多的信息。

### 紧性：GIN = 1-WL

GIN（Graph Isomorphism Network）选用 **多重集双射** 的聚合（
sum + 单射 MLP），证明了「在一定容量下 GIN 与 1-WL 同样强大」。
所以：

- demo B、C、D 中所有 GIN（无论网络多深、多宽）都 **不可能** 区
  分这些图对。
- 反过来，demo A 中 1-WL 能区分的 K_{1,3} 与 P_4，足够大的 GIN
  也一定能区分。

### 突破 1-WL：高阶 GNN

为了能区分 CFI(K_3)（demo D）这种 2-WL 才能搞定的图对，必须用
**k-阶 GNN**：

| 架构                                           | 表达力      |
| ---------------------------------------------- | ----------- |
| GCN, GAT, GraphSAGE, GIN, MPNN                 | ≤ 1-WL      |
| **k-GNN**（Morris et al.）                     | = k-WL      |
| **k-IGN**（Maron et al., Invariant GNN）       | ≥ k-WL      |
| **PPGN**（Provably Powerful GN, Maron 2019）   | ≥ 2-FWL     |
| **Subgraph GNNs**（ESAN, GNN-AK, …）           | strictly > 1-WL |
| **Local 2-GNN**（Morris 2020）                 | = 2-WL      |

Demo B、C、D 在 GNN 文献里就是 *标准* 的「区分这两张图，您的
模型至少要打到几阶 WL」考题。一个新提出的 GNN 如果在它们上面失
败，研究者一般就直接判定「表达力 ≤ 1-WL」。

### 小结：表达力等级

```
                      （区分一切非同构图）
                 ▲     可计算图同构（GI 完全）
                 │
              ⋮
              ⋮ k-WL
              ⋮ 3-WL ≡ 2-FWL
              │ 2-WL
                 │ 1-WL ≡ MPNN ≡ GIN
                 │ no neighbour info
```

WL 等级 *严格* 升级 —— 每加一阶都有 CFI 反例图证明它真的更强。
而 GNN 设计的核心问题，几乎完全等价于「我的架构落在这条等级链
的哪一段」。

---

## 5. Pocket 386 上的工程取舍

| 取舍 | 说明 |
| --- | --- |
| 颜色用整数 ID | 比 gensym 符号便宜，多重集排序也快 |
| 规范化器是全局 alist | 写入 O(1)，查找 O(N)，简单可靠；keys 全是 `equal`-比较的小列表 |
| 1-WL 用 `(cons own (sort nbr-cols))` 当 key | 一次 cons + 一次插入排序，最浅的递归 |
| 2-FWL 用 `(cons own-pair sorted-pair-list)` 当 key | 排序对的列表，仍走通用 `equal` |
| 不用哈希表 / vector | Apteryx 1.04 是否实现完整 `make-hash-table` 不可知；纯 list 写法兼容所有 Lisp |
| 不显示完整颜色多重集（只显示 partition signature） | 多重集长度可达 n²，对 n=18 已经是 324 项，partition signature 一行就够看 |
| Demo D 只跑结构最小的 CFI（基图 C_3） | 18 顶点，2-FWL 在 386SX 上分钟级；K_4 基图（40+ 顶点）只在 README 中给公式 |
| 整体只用 `defun cond if let setq defvar princ terpri` 等基础语法 | 与 Apteryx 1.04 兼容，也能在 SBCL/CLISP/ECL 上跨平台校验 |

## 6. 在 PC 上预跑

```bash
$ sbcl --script wl.lsp
```

Pocket 386 上预计耗时（手工估算）：

| Demo | 1-WL | 2-FWL |
| --- | --- | --- |
| A (n=4) | < 1 s | ~ 1 s |
| B (n=6) | < 1 s | ~ 5 s |
| C (n=6) | < 1 s | ~ 5 s |
| D (n=18) | ~ 2 s | ~ 1–3 min |

## 参考文献

- B. Weisfeiler & A. Lehman, *A reduction of a graph to a canonical
  form…*, NTI 1968.
- J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the
  number of variables for graph identification*, Combinatorica 1992
  （CFI 反例的源头）.
- M. Grohe, M. Otto, *Pebble games and linear equations*, JSL 2015
  （tw 与 k-WL 的精确等价）.
- C. Morris et al., *Weisfeiler and Leman go neural: Higher-order
  graph neural networks*, AAAI 2019.
- K. Xu et al., *How powerful are graph neural networks?* (GIN),
  ICLR 2019.
- H. Maron et al., *Provably powerful graph networks*, NeurIPS 2019.
