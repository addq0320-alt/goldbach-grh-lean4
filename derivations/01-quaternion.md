# 哥德巴赫谱假设的 Lean 4 验证

本项目检查李嘉旻、刘建亚所定义的四元数谱零点与谱大小之间的关系，并研究一个算术范数下界能排除哪些无零区。项目使用 Lean 4.19.0 和同版本 Mathlib。`../lean/verification/audit.txt` 记录构建与公理检查的实际输出。

**算术结论的范围。** 对真实哥德巴赫算子，强假设 R 的反证以 Yilin Liu 预印本的范数下界为前提。弱假设 S 在 `h(N) = log log N` 时需要的算术抵消界仍未证明。项目形式化了下界的一项 Buchstab 函数引理，并给出了可以精确验证抵消的测试区域。原论文的 Hardy 空间构造、从素数分布得到范数下界的完整论证，以及二元哥德巴赫猜想均未在项目中形式化。

## 复现

安装 elan 后，在含 `lean-toolchain` 的目录中运行以下命令。`lake-manifest.json` 固定了全部依赖版本。首次运行会下载依赖。

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true SpectralAudit.lean
```

`SpectralAudit.lean` 检查八个模块的全部 28 个公开定理，遍历每个定理证明的传递公理依赖。允许的基础公理为 `propext`、`Classical.choice` 和 `Quot.sound`。未完成证明或额外公理会使这一步报错。函数参数和定理前提仍应按各自的数学含义审读。

## 四元数零点和范数

设 `s = 𝔖(N)`，`L = log N`，`δ² = s L³ / N`，`μⱼ` 为实特征值，`wⱼ = 4 μⱼ² / δ²`。对非负、可和的权重 `w`，`Product.lean` 在每个复切片上取真正的无穷乘积，再将结果送回实四元数代数 `ℍ[ℝ]`。其中 `spectralQuaternion_zero_iff` 与 `quaternion_zero_iff` 把四元数值函数的零点同某个实际四元数因子的消失联系起来。

- `critical_iff` 证明所有零点实部等于 `1/2` 当且仅当对每个 `j` 有 `wⱼ ≤ 4`。
- `zeroFree_iff` 证明在 `0 < η ≤ 1/2` 时，开半空间 `Re(q) > 1−η` 无零点当且仅当对每个 `j` 有 `wⱼ η(1−η) ≤ 1`。零点可以落在边界上。
- `Obstruction.lean` 中的 `norm_dictionary` 将后一判据写成 `4 m² η(1−η) ≤ δ²`。其明确前提是 `m` 为特征值绝对值达到的最大值。对原论文的紧自伴算子，`m` 取其算子范数。有限谱可在序列末尾补零。

## 条件反证和弱假设的尺度

`log_square_refutes_R` 给出单个模数的结论。若 `0 < s ≤ L`，而某个特征值满足 `√N |μⱼ| > L²`，则存在实四元数零点 `x > 1/2`。

`obstruction_arbitrarily_large` 的算术前提 `hlower` 是，对任意自然数指数 `D` 和任意下界 `B`，存在偶数 `N ≥ B` 使 `√N m(N) > (log N)^D`。另有平方可和性、极值取到，以及对充分大的偶数成立的 `0 < 𝔖(N) ≤ log N`。以这些为输入，Lean 证明，对每个正整数 `k` 都有任意大的偶数及实零点满足

\[
     1-(\log N)^{-k} < x,\qquad X_N(x)=0.
\]

源码用 `k+1` 枚举正整数。不同 `k` 的偶数序列可以不同。证明从一个超过门槛的因子出发，用介值定理在开边界的右侧产生零点，无需数值求根。预印本的定理 1.1 声称从 Dirichlet GRH 得到上述范数下界。项目中该下界保留为定理参数。原论文中 `𝔖(N) ≪ log log N` 蕴含这里使用的较弱奇异级数上界。

`WeakS.lean` 包含两步正向推导。

- `weak_of_gain` 证明，只要 `|μⱼ| ≤ s/(2h)` 对所有特征值成立，就能得到原文规定的宽度 `η = h² L³ / (Ns)` 的无零区，适用于 `0 < η ≤ 1/2`。
- `model_weak_and_spikes` 取 `s=1`，只保留一个非零特征值 `1/log N`。对每个固定的自然数 `D`，当 `N` 充分大时，模型同时满足上述范数下界、`0 < η ≤ 1/4` 和 `h = log log N` 的弱无零区。这里的特征值和奇异级数是为检验逻辑蕴含而选定的模型数据。它说明大的归一化范数可以与该弱窗口相容。

## 真实算术核中可以精确消去的部分

`Cancellation.lean` 检查尺度变量 `m/N` 和 `n/N` 同时落在 `(0,1/2)` 或同时落在 `(1/2,1)` 的情形。此时同余 `m ≡ n (mod N)` 只剩对角项，且 `N` 不整除 `m+n`。`same_side_arithmetic_zero` 因而得到扣除对角项的有符号同余核逐点为零。乘上冯·曼戈尔特权及互素条件后仍然为零。

`same_side_beta_zero` 验证同侧支撑的两个测试函数在每个正整数平移 `k` 上满足

\[
 f(u)g(u+k)+g(u)f(u+k)-f(u)g(k-u)=0.
\]

所以对应 Beta 模型的每个此类积分也为零。此结论针对同一开半区的测试。落在相反半区时，`m+n=N` 可以成立；这些混合项直接包含待估的素数对相关。完整 Hardy 空间还允许其他尺度的测试。

`KernelTest.lean` 给出全算子范数的一个严格检验。取核向量 `vᵢ`，假定其有限线性组合稠密，记 `v(a) = ∑ aᵢ vᵢ`。对每个 `B ≥ 0`，`norm_le_iff_finite_tests` 证明 `‖T‖ ≤ B` 等价于对每一对有限系数列成立

\[
 \Big|\sum_{i,j}\overline{a_i}b_j\langle v_i,Tv_j\rangle\Big|
 \le B\,\|v(a)\|\,\|v(b)\|.
\]

取 `T=T_N`、`B=𝔖(N)/(2 log log N)` 就得到一个足以推出目标弱无零区的算术估计。这里需要同一常数控制所有有限组合。单一网格上的成功不能给出这个上界。Lean 使用对第二变量线性的内积。

## 真实算子的区间恒等式与范数扰动

`Interior.lean` 证明在整数区间 `0 < m,n < N` 内，有符号同余核逐项等于 `-1` 乘以 `m+n=N` 的示性函数。对任意实权重，`interior_double_sum` 把相应双重和精确化为沿 `n=N-m` 的负的单和，涵盖真实算子的冯·曼戈尔特权与互素条件。`short_signed_kernel` 给出 `2X<N` 时短和的逐项消去。`interior_beta_reflection` 验证两个支撑在 `(0,1)` 的独立复值测试函数在 Beta 模型中只留下整数平移 1 的反射项。

`Covariance.lean` 中的 `covariance_difference` 和 `covariance_sum_difference` 在复内积空间中估计用近似向量代替原向量时，单个秩一算子与其有限加权和的算子范数误差。取均匀权重即可用于奇特征平均。GRH 下的 Dirichlet 级数尾界、完整的 Hilbert–Schmidt 范数估计和平衡压缩的奇异值衰减由配套笔记给出解析证明。

## 预印本中的 Buchstab 函数引理

`Buchstab.lean` 的 `buchstab_gap_unbounded` 从 `ω(t)=1/t`（`1<t<2`）和 `t ω′(t)=ω(t−1)−ω(t)`（`t>2`）证明，任意给定 `A`，都存在 `u>A` 满足 `ω(u)>ω(u+1)`。若所有大 `u` 都满足反向不等式，微分方程会先迫使函数在尾部单调递减，再迫使它在尾部为常数。将该常数区间逐次向左延长，与初始值矛盾。此引理检查了预印本第 3 节式 (6) 的参数选择；从这一步到范数下界还需要粗数密度、短区间素数估计、算术级数平均以及与 Hardy 核的对应。

## 原始文献

1. 李嘉旻、刘建亚，*A Conditional Proof of the Goldbach Conjecture*，2026-11-13。谱乘积见式 (1.6)，范数判据见式 (2.28)、(2.30)。[山东大学原文与 PDF](https://mrc.sdu.edu.cn/english/info/1018/1514.htm)
2. Yilin Liu，*Failure of the Li–Liu spectral hypothesis R under Dirichlet GRH*，2026-11-21，v1。条件范数下界见定理 1.1，Buchstab 引理见第 3 节。[预印本与版本说明](https://hexagonmath.org/2611.00788v1)
