# pocket-386-lisp

为 **Pocket 386** 上的 **Apteryx Lisp** 编写的 DPLL（Davis–Putnam–
Logemann–Loveland）SAT 求解器，附带几个用于演示的简单命题。

## 目标硬件 / 解释器

| 项目      | 规格                                                        |
| --------- | ----------------------------------------------------------- |
| CPU       | ALi M6117（80386SX 内核，约 25–40 MHz，无 FPU）             |
| 内存      | 8 MB DRAM                                                   |
| 显存/显卡 | CL-GD542X / TVGA9000 / CHIPS F655xx                          |
| 存储      | CF 卡（IDE 模式），FAT16，文件名受 8.3 限制                  |
| 操作系统  | DOS 6.22 / Windows 3.11 / Windows 95                         |
| 解释器    | Apteryx Lisp 1.04（1994，运行于 Win 3.x，可在 Pocket 386 上运行） |

## 文件

```
dpll.lsp     主程序：DPLL 实现 + 6 个测试命题 + 调用 (run-tests)
README.md    本说明
```

文件名遵守 **8.3 命名规则**，扩展名 `.lsp` 是 DOS 时代 Lisp 源码的
惯用扩展名，Apteryx Lisp 也能直接 `LOAD` 它。

## 在 Pocket 386 上运行

1. 用 CF 卡或串口把 `dpll.lsp` 拷到机器，例如 `C:\LISP\DPLL.LSP`。
2. 在 Windows 3.11 中启动 **Apteryx Lisp**。
3. 在 Listener（解释器交互窗口）输入：

   ```lisp
   (load "c:\\lisp\\dpll.lsp")
   ```

   文件末尾已经写了 `(run-tests)`，加载后会自动跑完 6 个命题。
   想再跑一次，直接键入 `(run-tests)` 即可。

## 关于硬件约束的取舍

Pocket 386 的资源比一台 1990 年代的工作站还紧，写 Lisp 时要避免
任何会大量分配 cons 单元的写法。下面这些选择都是直接为 8 MB /
386SX 服务的：

1. **整数编码命题变量**
   变量是 `1..N` 的正整数，文字（literal）就是带符号整数：`5` 表示
   `x5`，`-5` 表示 `¬x5`。这样一个文字只占 **一个 fixnum**（不分配
   cons），子句也只是普通整数列表，比 `(NOT x)` 这种符号包装节省
   一半以上的堆。
2. **只用最基本的特殊形式**
   只用 `defun / cond / if / and / or / let / quote`，不用 `let*`、
   `loop`、`format` 指令、关键字参数或宏。1994 年的 Apteryx Lisp 体
   积小，未必实现完整的 ANSI CL，少用花哨语法最稳。
3. **不调用 `remove` / `find` / `mapcar` 等序列函数**
   自己写 `mem-int`、`del-int` —— 因为某些精简 Lisp 的 `remove` 会
   先复制再过滤，临时垃圾很多；手写 `cdr` 递归只在必要时分配新 cons。
4. **省略纯文字（pure literal）消去**
   纯文字消去要扫描整个公式统计极性，代价不低。对手册级的小命题，
   只用 **单元传播 + 分支回溯** 已经够快，少一遍扫描就少一次堆压力。
5. **分支启发式选最简单的**
   `pick-lit` 直接拿第一个子句的第一个文字。MOMS、VSIDS 之类的启发
   式要维护额外计数表，对 8 MB 内存的机器不划算；对 < 20 个变量的
   小命题，简单选择已经能秒出。
6. **递归深度可控**
   求解过程递归深度 ≤ 命题中变量数 + 单元传播步数。本仓库的 6 个
   测试命题最多 9 个变量，386SX 上栈深度不会有问题。
7. **输出极简**
   `princ` + `terpri` 手动拼字符串，不用 `format`。Apteryx Lisp 的
   `format` 实现可能不完整，并且解析格式串本身也消耗内存。

## 已实现的命题

文件中的 `run-tests` 会顺序求解 6 个小命题，覆盖 SAT / UNSAT 两种
情况：

| 编号 | 命题                                                | 期望结果 |
| ---- | --------------------------------------------------- | -------- |
| P1   | `(A ∨ B) ∧ (¬A ∨ B)`                                | SAT      |
| P2   | `A ∧ ¬A`                                            | UNSAT    |
| P3   | `(A ∨ B) ∧ (¬A ∨ C) ∧ (¬B ∨ ¬C)`                    | SAT      |
| P4   | `(P → Q) ∧ (Q → R) ∧ P ∧ ¬R`（modus ponens 矛盾）    | UNSAT    |
| P5   | 3 只鸽子塞 2 个洞（鸽笼原理）                       | UNSAT    |
| P6   | 3 只鸽子塞 3 个洞                                   | SAT      |

## 在 Pocket 386 上的预期输出

```
DPLL on Pocket 386 / Apteryx Lisp
=================================

---- P1  (A v B) and (~A v B) ----
 CNF : (1 2) ^ (-1 2)
 RES : SAT  { 2 1 }

---- P2  A and ~A ----
 CNF : (1) ^ (-1)
 RES : UNSAT

---- P3  (A v B) ^ (~A v C) ^ (~B v ~C) ----
 CNF : (1 2) ^ (-1 3) ^ (-2 -3)
 RES : SAT  { -2 3 1 }

---- P4  (P->Q) ^ (Q->R) ^ P ^ ~R ----
 CNF : (-1 2) ^ (-2 3) ^ (1) ^ (-3)
 RES : UNSAT

---- P5  pigeonhole 3-in-2 (UNSAT) ----
 CNF : (1 2) ^ (3 4) ^ (5 6) ^ (-1 -3) ^ ... ^ (-4 -6)
 RES : UNSAT

---- P6  pigeonhole 3-in-3 (SAT) ----
 CNF : (1 2 3) ^ (4 5 6) ^ (7 8 9) ^ ... ^ (-6 -9)
 RES : SAT  { -6 -3 9 -8 -2 5 -7 -4 1 }

done.
```

模型读法：列出来的每个文字都为真。例如 P6 中
`{-6 -3 9 -8 -2 5 -7 -4 1}` 表示
`x11=T, x22=T, x33=T`（其余编号为假）—— 即第一只鸽子进 1 号洞，第
二只鸽子进 2 号洞，第三只鸽子进 3 号洞，正好是一个对角线分配。

## 自己加新命题

```lisp
;; 例：(A ∨ B ∨ C) ∧ (¬A) ∧ (¬B)   -> 应为 SAT, C=T
(solve "my-test" '((1 2 3) (-1) (-2)))
```

变量编号必须从 1 开始连续使用，正/负号代表极性。Apteryx Lisp
里直接在 Listener 输入上面那行就能跑。

## 在 PC 上预先校验

如果手头有 SBCL / CLISP / ECL，可以先在 PC 上验证逻辑：

```bash
sbcl --script dpll.lsp
```

代码只用 ANSI CL 的最小子集，所以在大多数 Lisp 实现上都能直接运行；
然后再把同一份 `dpll.lsp` 拷到 Pocket 386 上让 Apteryx Lisp 跑。
