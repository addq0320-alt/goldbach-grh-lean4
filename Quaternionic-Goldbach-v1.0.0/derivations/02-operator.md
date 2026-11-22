# 哥德巴赫算子的三个范数估计

<small>原稿第 1 页</small>

对李嘉旻、刘建亚的算子 $T_N=P_N-D_N-K_N$，以下考虑平衡素数对所在的子空间、全空间的算术截断误差，以及 Hardy 带的右边界块。设 $N$ 是充分大的偶数，$\operatorname{GRH}(N)$ 对模 $N$ 的 Dirichlet 特征成立，记

$$
 L=\log N,\qquad \alpha=1/L,\qquad \beta=1/8,\qquad S=\mathfrak S(N).
$$

$S=2C_2\prod_{p\mid N,\,p>2}(p-1)/(p-2)$ 为哥德巴赫奇异级数。$H_N$ 是带 $\alpha<\Re s<\beta$ 的 Hardy 边界迹空间，两条边界均取弧长测度。原文式 (2.28) 给出弱谱假设的精确目标，取 $h=\log L$ 有

$$
 \|T_N\|\ \le\ \frac{S}{2h\sqrt{1-\eta_N}},\qquad
 \eta_N=\frac{h^2L^3}{NS}.
$$

以下 $\|\cdot\|$ 指算子范数或向量范数，$\|\cdot\|_{\mathrm{HS}}$ 指 Hilbert–Schmidt 范数。各估计中的常数与 $N$ 无关。[1]

## 1　平衡区间上的真实算子

令 $I=(1/3,2/3)$。对 $f\in C_c^\infty(I)$，令 $v_f$ 表示原文的 Mellin 测试泛函。具体地，若 $\Phi_f(u)=\sqrt{u}\,f(u)$，$\widehat\Phi_f(s)=\int_0^\infty\Phi_f(u)u^{s-1}\,du$，则测试泛函在 $\alpha<\sigma\le 1/9$ 上取值

$$
 \langle h,v_f\rangle=\frac{1}{2\pi i}\int_{(\sigma)}
        N^s(1+s)\widehat\Phi_f(s)h(s)\,ds.
$$

沿用内积对第一变量线性的约定。令 $V$ 为所有 $v_f$ 的闭包，$\Pi_I$ 为到 $V$ 的正交投影，$B_N=\Pi_I T_N|_V$。在 $I$ 上定义两个测度

$$
 \nu_N=\frac1N\sum_{\substack{m/N\in I\\(m,N)=1}}\!
  \Lambda(m)\Lambda(N-m)\,\delta_{m/N},
 \qquad \rho_N=S\,du-\nu_N.
$$

对独立的复值测试函数 $f,g$，压缩算子的混合矩阵元满足

$$
 \boxed{\ \langle B_Nv_g,v_f\rangle
    =\int_I f(u)\overline{g(1-u)}\,d\rho_N(u).\ }\tag{1}
$$

**推导。** 将两个测试泛函分别作用于核的两个变量。对特征部分，在 GRH 下将积分移到绝对收敛线；Mellin 反演给出 $N^{-1} f(m/N)\overline{g(n/N)}$。奇特征正交性给同余类 $m\equiv n$ 正号、$m\equiv -n$ 负号。因 $0<m,n<N$，前者恰为 $D_N$ 的对角，后者恰为 $m+n=N$。于是 $P_N-D_N$ 给出式 (1) 的 $-\nu_N$ 项。[1, §7；2, §2]

对 Beta 模型，将 $f,g$ 在 $I$ 外延零。三个 Beta 积分反演为正整数 $k$ 上的两个差平移与一个负的反射。移动 Mellin 积分线时，可能的极点 $w=1$ 被消去，因为对全部正平移量积分，两个差平移恰覆盖整个 $(u,v)$ 正象限，而反射减去同一积分。在整数 $k\ge1$ 上，两个差平移均为零，反射仅余 $k=1$，系数为 $S$。代入 $-K_N$ 正好给出 $+S\,du$。此论证也适用于互不对称的 $f,g$。[1, 引理 7.2；2, §2]



## 2　奇异值衰减及首个方向的障碍

<small>原稿第 2 页</small>

**命题 A。** 将 $B_N$ 的奇异值按降序记作 $s_j(B_N)$，在上述假设下，

$$
 \boxed{\quad s_j(B_N)\ \ll\ \frac{S}{j^2}\qquad(j\ge1).\quad} \tag{2}
$$

**证明。** 测试向量的精确范数为 [1, 命题 7.4；2, 式 (2)]

$$
 \|v_f\|^2=\frac1{2\pi}\int_I
 \frac{(Nu)^{2\alpha}}{1+(Nu)^{-2(\beta-\alpha)}}
       |f(u)/2-uf'(u)|^2\,du .
$$

因 $u\in I$ 且 $N^{2\alpha}=e^2$，分式一致地夹在两个正常数之间。分部积分给出 $\int_I|f/2-uf'|^2=\int_I(u^2|f'|^2+3|f|^2/4)$。因此 $\|v_f\|\asymp\|f\|_{H_0^1(I)}$。式 (1) 按连续性延拓到 $H_0^1(I)$。

取正测度 $\lambda=S\,du+\nu_N$，有 $|\rho_N|\le\lambda$，且 $\lambda$ 关于 $u\mapsto1-u$ 对称。Selberg 上界筛给出有序素数对 $\#\{p+q=N\}\ll NS/L^2$；每项权重至多 $L^2$。至少一项为高次素数幂的有序对至多 $O(\sqrt N L)$ 个，故其归一化权重为 $O(N^{-1/2}L^3)$。由 $S\ge 2C_2>0$ 得 $M=\lambda(I)\ll S$。[3]

固定整数 $k\ge1$。将 $I$ 的 $k$ 等分点与 $\lambda$ 的 $j/k$ 分位点（$1\le j<k$）合并。每个开子区间 $J$ 的长度至多 $|I|/k$，测度至多 $M/k$；有原子时用左右端点间的开区间，端点原子在下述测试上取零。具体地，取第 $j$ 个分位点为使 $\lambda((1/3,x])\ge jM/k$ 的最小 $x$，重复节点只算一次。

令 $F\subset V$ 对应于所有在这些节点取零的函数。点值连续，且 $\operatorname{codim} F\le2(k-1)$。在每个 $J$ 上，$\sup_J|f|^2\le |J|\int_J|f'|^2$。求和得

$$
 \int_I |f|^2\,d\lambda \ \ll\ M k^{-2}\|v_f\|^2 \qquad(v_f\in F).
$$

令 $Q$ 为到 $F$ 的正交投影。在 (1) 中用 Cauchy–Schwarz 和 $\lambda$ 的反射对称性，得到 $\|QB_NQ\|\ll M/k^2$。差 $B_N-QB_NQ=(1-Q)B_N+QB_N(1-Q)$ 的秩至多 $4(k-1)$。由紧算子奇异值的逼近刻画，$s_{4k-3}(B_N)\ll M/k^2$。奇异值单调，故得 (2)。特别地，此区间至多有 $O(\sqrt{\log\log N})$ 个奇异值可以超过 $S/(2\log\log N)$。

**最大奇异值与累计偏差。** 令 $a=1/3$，$D(x)=S(x-a)-\nu_N((a,x])$，$\overline D_U=|U|^{-1}\int_U D$。对任意固定开区间 $J$ 满足 $\overline J\subset I$，有

$$
 \|D-\overline D_J\|_{L^2(J)}
    \ \ll_J\ \|B_N\|\ \ll\ \|D-\overline D_I\|_{L^2(I)}. \tag{2a}
$$

设 $H(u)=f(u)\overline{g(1-u)}$。因 $H$ 两端取零，式 (1) 分部积分等于 $-\int_I(D-\overline D_I)H'$。一维 Sobolev 嵌入给 $\|H'\|_2\ll\|v_f\|\|v_g\|$，得到右界。为证左界，取固定光滑 $g$ 在 $1-J$ 上恒为一且支撑于 $I$。取 $f$ 在 $J$ 上为 $D-\overline D_J$ 从左端点起的原函数，在 $J$ 外延零。它属于 $H_0^1(I)$，而 $|\int f\,d\rho_N|=\|D-\overline D_J\|_2^2$、$\|v_f\|\ll\|D-\overline D_J\|_2$。代入 (1) 即得。

若某个 $N$ 在 $I$ 内没有素数对，则高次素数幂的上界给出 $D(x)=S(x-a)+O(N^{-1/2}L^3)$。对固定 $J$，线性函数减均值后的 $L^2(J)$ 范数是 $S|J|^{3/2}/\sqrt{12}$。故此时 $\|T_N\|\ge\|B_N\|\gg_J S$。上界筛无法排除这一情形。



## 3　全空间的算术截断误差

<small>原稿第 3 页</small>

令 $\mathbb{E}^-_\chi$ 表示模 $N$ 奇特征的均值，包括非本原特征。记

$$
 d_n(s)=\frac{n^{-s}}{1+s},\qquad
 F_\chi(s)=-\frac{1}{1+s}\frac{L'}{L}\bigl(\tfrac12+s,\chi\bigr),\qquad
 F_{\chi,X}=\sum_{n\le X}\frac{\Lambda(n)\chi(n)}{\sqrt n}\,d_n .
$$

原文的特征算子为 $P_N=\mathbb{E}^-_\chi F_\chi\otimes F_\chi$，令 $P_X=\mathbb{E}^-_\chi F_{\chi,X}\otimes F_{\chi,X}$。对角算子 $D_N$ 是 $\sum_{(n,N)=1}\Lambda(n)^2 n^{-1}d_n\otimes d_n$，令 $D_X$ 为 $n\le X$ 的部分。$u\otimes v$ 表示 $h\mapsto\langle h,v\rangle u$。[1, §6.4]

**命题 B。** 保留完整的 Beta 算子 $K_N$，取 $X=N^{8\log L}$，则

$$
 \boxed{\quad
 \|T_N-(P_X-D_X-K_N)\|_{\mathrm{HS}}\ \ll\ L^{-2}.
 \quad} \tag{3}
$$

**证明。** GRH 的显式公式给每个奇特征一致的界
$|A_\chi(u)|\ll\sqrt u\,\log^2(2Nu)$，其中 $A_\chi(u)=\sum_{n\le u}\Lambda(n)\chi(n)$。奇特征均非主特征，故无主项。[4, 定理 13.7]
取 $w=1/2+s$，由分部求和，

$$
 (1+s)(F_\chi-F_{\chi,X})(s)
  =-A_\chi(X)X^{-w}+w\int_X^\infty A_\chi(u)u^{-w-1}\,du.
$$

在 $\Re s=\sigma$ 上取 $L^2(dt)$ 范数。积分中令 $y=\log u$，再用 Plancherel 和 $|w/(1+s)|\le1$；端点项用 $\int_{\mathbb{R}} |1+\sigma+it|^{-2}\,dt=\pi/(1+\sigma)$。积分项的范数平方至多为常数乘

$$
 \int_{\log X}^{\infty} e^{-2\sigma y}(L+1+y)^4\,dy
 \ll X^{-2\sigma}\sigma^{-1}(L+\log(2X)+\sigma^{-1})^4 .
$$

由此对 $X\ge1,\ \alpha\le\sigma\le\beta$，得到

$$
 \|F_\chi-F_{\chi,X}\|_{2,\sigma}
  \ll X^{-\sigma}\sigma^{-1/2}(L+\log(2X)+\sigma^{-1})^2. \tag{4}
$$

取 $X=1$ 得 $\|F_\chi\|_{H_N}\ll L^{5/2}$。取命题中的 $X$ 则 $X^{-\alpha}=L^{-8}$，两条线上合计的尾向量范数 $\epsilon\ll L^{-11/2}(\log L)^2$。利用秩一差的 HS 界 $(2\|F_\chi\|+\epsilon)\epsilon$ 并平均，得 $\|P_N-P_X\|_{\mathrm{HS}}\ll L^{-3}(\log L)^2$。

由 $\sum_{n\le u}\Lambda(n)^2\ll u\log(2u)$ 及
$\|d_n\|^2=\pi\sum_{\sigma=\alpha,\beta}n^{-2\sigma}/(1+\sigma)$，分部求和得到

$$
 \|D_N-D_X\|_{\mathrm{HS}}\le \operatorname{tr}(D_N-D_X)
 \ll X^{-2\alpha}\bigl(\alpha^{-1}\log(2X)+\alpha^{-2}\bigr)
 \ll L^{-14}\log L .
$$

两界相加得到 (3)。因为算子范数不超过 HS 范数，这也给出了 $\|T_N\|$ 与 $\|P_X-D_X-K_N\|$ 之差的上界。有限化的是算术和；$K_N$ 在等式两侧完全相同。



## 4　右边界上的幂次上界

<small>原稿第 4 页</small>

令 $\widetilde T_N=T_N\oplus0$ 表示在整个双边界 $L^2(\Gamma_N)$ 上的核算子，$Q_\beta$ 是到 $\Re s=\beta$ 这一分量的正交投影。定义投影所在空间很重要，因为单独取一条边界的函数一般不再是同一个全纯函数的双边界迹。[1, §5]

**命题 C。** 当 $\beta=1/8$ 时，两端都投影到右边界的算子满足

$$
 \boxed{\quad \|Q_\beta\widetilde T_N Q_\beta\|_{\mathrm{HS}}
       \ \ll\ N^{-1/8}(\log N)^2 .\quad} \tag{5}
$$

**证明。** 取 $X=N/3$。对 $m,n\le X$ 且 $(mn,N)=1$，奇特征正交性给

$$
 \mathbb{E}_\chi^-\chi(m)\overline{\chi(n)}
 =\mathbf{1}_{m\equiv n\bmod N}-\mathbf{1}_{m\equiv -n\bmod N}
 =\mathbf{1}_{m=n}.
$$

故 $P_X=D_X$。在右线上，$\mathbb{E}^-_\chi\|F_{\chi,X}\|_{2,\beta}^2=\operatorname{tr}(Q_\beta D_X Q_\beta)\ll\sum_n\Lambda(n)^2 n^{-1-2\beta}\ll1$。式 (4) 给 $\|F_\chi-F_{\chi,X}\|_{2,\beta}\ll N^{-\beta}L^2$。将秩一差估计为 $(2\|F_{\chi,X}\|_{2,\beta}+\epsilon)\epsilon$，再对特征用 Cauchy–Schwarz，得 $P_N-P_X$ 的右边界块为 $O(N^{-\beta}L^2)$，此处及下文均取 HS 范数。对角尾项为 $O(N^{-2\beta}L)$。

对 Beta 核用原文式 (6.16)。两变量的实部都为 $\beta$ 时，
$\prod_{p>2,\,p\nmid N}(1+p^{-w}/(p-2))$ 在 $\Re w=2\beta$ 一致有界；两个 Gamma 比一致有界；$\zeta(1-2\beta-it)\ll(2+|t|)^{2\beta}$。除以 Hardy 核的归一化因子后，模型核绝对值被下式控制：

$$
 C S N^{-2\beta}\,
 \frac{(2+|t-y|)^{2\beta}}{\sqrt{(1+t^2)(1+y^2)}} .
$$

右侧平方可积，因为 $4\beta=1/2<1$。于是 $K_N$ 的右边界块为 $O(SN^{-2\beta})$；由 $S\ll\log\log N$，与前两项合并即得 (5)。[1, §6.4]

**全算子还差什么。** 在左线上，同一截断只有 $(N/3)^{-\alpha}\to e^{-1}$；式 (4) 无法给出所需的节省。式 (3) 虽可精确逼近全算子，剩下的有符号算术和与 $K_N$ 的抵消仍包括非对角的加法相关。命题 A 也只控制一个压缩的奇异值尾部。本文未从 GRH 推出弱谱假设的全空间范数上界。

### 文献与形式化范围

[1] Jiamin Li、Jianya Liu，*A Conditional Proof of the Goldbach Conjecture*，式 (2.28)，§§5–7。[山东大学原文](https://mrc.sdu.edu.cn/english/info/1018/1514.htm)  
[2] Yilin Liu，*Failure of the Li–Liu spectral hypothesis R under Dirichlet GRH*，v1，§2。此处仅用其混合测试计算和范数公式。[预印本](https://hexagonmath.org/2611.00788v1)  
[3] R. C. Vaughan，*The Selberg Sieve*，二元哥德巴赫有序素数对的上界。[课程讲义](https://personal.science.psu.edu/rcv4/571s25/Class571-04.pdf)  
[4] H. L. Montgomery、R. C. Vaughan，*Multiplicative Number Theory I: Classical Theory*，定理 13.7。[书目与原文](https://www.ndl.ethernet.edu.et/bitstream/123456789/23715/1/Hugh%20L.%20Montgomery.pdf)

配套 Lean 工程检查了短和消去、区间内双重和化为反射单和、Beta 模型的整数平移选择，以及有限秩一和的算子范数扰动界。命题 A–C 的完整解析证明见本文。
