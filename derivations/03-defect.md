# 哥德巴赫压缩算子的例外集

<small>原稿第 1 页</small>

设 $I=(1/3,2/3)$，$N$ 为充分大的偶数，$S_N=\mathfrak S(N)$ 为二元哥德巴赫奇异级数，$B_N$ 为李–刘算子在 $I$ 的 Mellin 测试向量所生成闭子空间上的正交压缩。本文假设全体 Dirichlet $L$ 函数的 GRH。圆法部分会用到与 $N$ 不同的模数。

**定理 1（例外集）。** 对每个固定的 $A>0$ 和 $\varepsilon>0$，有

$$
 \boxed{\quad
 \#\{X\le N\le 2X:\ 2\mid N,\ \|B_N\|>S_N(\log X)^{-A}\}
 \ll_{A,\varepsilon} X^{2/3+\varepsilon}.\quad} \tag{1}
$$

**定理 2（逐偶数判据）。** 沿任意趋于无穷的偶数序列，$\|B_N\|/S_N\to0$ 当且仅当每个固定的 $\psi\in C_c^\infty(I)$ 都满足

$$
 \frac1{NS_N}\sum_{\substack{m/N\in I\\(m,N)=1}}
   \Lambda(m)\Lambda(N-m)\psi(m/N)\ \longrightarrow\ \int_I\psi(u)\,du . \tag{2}
$$

为证定理 2，令 $\nu_N$ 为 (2) 左侧的归一化原子测度乘 $S_N$，记 $\rho_N=S_N\,du-\nu_N$。前篇《哥德巴赫算子的三个范数估计》式 (1)、(2a) 给出

$$
 \langle B_Nv_g,v_f\rangle
   =\int_I f(u)\overline{g(1-u)}\,d\rho_N(u),\qquad
 \|v_f\|\asymp\|f\|_{H_0^1(I)}. \tag{3}
$$

常数与 $N$ 无关。给定 $\psi$，取 $f=\psi$，令光滑 $g$ 在 $1-\operatorname{supp}\psi$ 上恒为一且支撑于 $I$。式 (3) 表明 $\|B_N\|/S_N\to0$ 推出 (2)。

反过来，Selberg 素数对上界和高次素数幂的平凡估计给出 $\|\rho_N\|_{\mathrm{TV}}\ll S_N$。所以 (2) 可由稠密性延拓到 $C_0(I)$ 中每个固定函数。对 $\|v_f\|,\|v_g\|\le1$，测试乘积 $f(u)\overline{g(1-u)}$ 在闭区间上一致有界、在端点取零，并有一致的 $1/2$ 阶 Hölder 界。这由 $|f(u)-f(v)|\le |u-v|^{1/2}\|f'\|_2$ 得到。所有 $N$ 的这些乘积并在一起，按 Arzelà–Ascoli 有紧闭包。用有限一致范数网覆盖它，并用总变差界控制网内误差；式 (2) 在整个乘积类上一致成立。对 (3) 取上确界即证。

因此，若某个序列上 $\|B_N\|\ge cS_N$（固定 $c>0$），可取子序列和**一个固定的**光滑权函数，使 (2) 的误差持续有正下界。另一方面，若 (2) 对全部充分大偶数成立，则对每个固定区间 $J\Subset I$，光滑上下逼近给出其中有序素数对数的渐近式 $S_N|J|N/(\log N)^2$。这里高次素数幂的归一化贡献是 $O(N^{-1/2}\log^3 N)$；对 $p/N\in J$，$\log p$ 和 $\log(N-p)$ 都是 $\log N+O(1)$。这解释了逐点排除缺陷所需结论的强度。[1, 2]



## 主弧在每个偶数上的贡献

<small>原稿第 2 页</small>

以下证明定理 1。取 $H=2X$，$L=\log(2X)$，$e(t)=\exp(2\pi it)$。令 $0\le y\le H$，$X\le N\le H$，定义

$$
 F_y(\theta)=\sum_{m\le y}\Lambda(m)e(m\theta),\qquad
 V_y(\beta)=\int_0^y e(\beta t)\,dt .
$$

对所有整数求和时，下文均要求素数权的自变量为正。令

$$
 R_y(N)=\sum_{\substack{m+r=N\\m\le y}}\Lambda(m)\Lambda(r)
       =\int_{\mathbb R/\mathbb Z}F_y(\theta)F_H(\theta)e(-N\theta)\,d\theta .
$$

取 $2\le Q\le X^{1/3}$。对既约 $a/q$、$q\le Q$，主弧取 $|\theta-a/q|\le2Q/(qX)$，距离按模一计算。因 $4Q^2<X$，这些弧互不相交。记它们的并为 $\mathfrak M$，补集为 $\mathfrak m$。

**特征估计。** 对 $q\le 2X$、$(a,q)=1$，部分求和给出

$$
 F_y(a/q+\beta)
 =\frac{\mu(q)}{\varphi(q)}V_y(\beta)
 +O\bigl(\sqrt{qX}\,L^2(1+X|\beta|)\bigr). \tag{4}
$$

证明如下。在单位剩余类上展开 $e(am/q)$，记未归一化特征系数为 $b_\chi$。正交性给 $\sum_\chi |b_\chi|^2=\varphi(q)^2$，主特征的系数是 $\mu(q)$。GRH 给出 $\sum_{m\le t}\Lambda(m)\chi(m)=\mathbf1_{\chi=\chi_0}t+O(\sqrt X L^2)$，对 $t\le H$ 一致。用 $\varphi(q)^{-1}\sum_\chi|b_\chi|\le\sqrt{\varphi(q)}$ 即得 $\beta=0$ 的误差。非单位项的总权至多 $\omega(q)L$，也包含在误差内。再对因子 $e(\beta m)$ 作部分求和，就得到 (4)。[3, 定理 13.7]

**主弧乘积误差。** 在两因子中代入 (4)，用 $|V_y(\beta)|\ll X/(1+X|\beta|)$。一个主项与一个误差的乘积，对固定 $a/q$ 至多为 $CX^{3/2}\sqrt q\,L^2/\varphi(q)$。乘弧长并对全部分数求和，两交叉项合计为

$$
 \ll \sqrt X\,Q L^2\sum_{q\le Q}q^{-1/2}
 \ll \sqrt X\,Q^{3/2}L^2 .
$$

两个误差的乘积，对固定分数的积分至多为

$$
 \ll qX L^4\int_{|\beta|\le 2Q/(qX)}(1+X|\beta|)^2\,d\beta
 \ll L^4 Q^3/q^2 .
$$

对分子、分母求和得 $O(Q^3L^5)$。两个估计对每个 $N$、每个 $y$ 同时成立。留下的主项系数是 $\mu(q)^2c_q(N)/\varphi(q)^2$，其中 $c_q$ 是 Ramanujan 和。



## 奇异级数的尾部与小弧均方

<small>原稿第 3 页</small>

将主项中的 $\beta$ 积分延至实线。由 $|V_yV_H|\ll|\beta|^{-2}$，固定 $q$ 的积分尾部是 $O(qX/Q)$。对任意 $\delta>0$，一致于 $N\le H$，有

$$
 \sum_{q\le Q}\frac{q\,|c_q(N)|}{\varphi(q)^2}\ll_\delta X^\delta,\qquad
 \sum_{q>Q}\frac{|c_q(N)|}{\varphi(q)^2}\ll_\delta X^\delta/Q. \tag{5}
$$

为核对 (5)，用 $|c_q(N)|\le(q,N)\le\sum_{d\mid q,\,d\mid N}d$ 和 $\varphi(q)^{-2}\ll_\eta q^{-2+\eta}$。写 $q=dr$ 后，第一式每个 $d\mid N$ 贡献 $O_\eta(Q^\eta)$；第二式对 $d\le Q$ 有 $d^{-1+\eta}\sum_{r>Q/d}r^{-2+\eta}\ll_\eta Q^{-1+\eta}$，对 $d>Q$ 同样成立。用 $\tau(N)\ll_\eta X^\eta$，选 $0<\eta<\min(1/2,\delta/3)$ 即可。

由傅里叶反演，$\int_{\mathbb R}V_y(\beta)V_H(\beta)e(-N\beta)d\beta=\min(y,N)$。当 $N$ 为偶数，$\sum_{q\ge1}\mu(q)^2 c_q(N)/\varphi(q)^2=S_N$，这也可由 $c_p(N)$ 在 $p\mid N$ 与 $p\nmid N$ 时分别为 $p-1$ 与 $-1$ 直接取 Euler 乘积得到。[4]

综合以上主弧估计，对所有这些 $N,y$，

$$
 \left|\int_{\mathfrak M}F_yF_H e(-N\theta)\,d\theta-S_N\min(y,N)\right|
 \ll_\delta \sqrt X Q^{3/2}L^2+Q^3L^5+X^{1+\delta}/Q . \tag{6}
$$

现在令 $a_0=A+2$，$Q=\lfloor X^{1/3}L^{-(2a_0+10)}\rfloor$。固定 $\delta=1/12$，(6) 为 $O_A(XL^{-a_0})$。到此为止没有舍弃任何偶数。

**小弧。** 对 $\theta\in\mathfrak m$，Dirichlet 有理逼近给出既约 $a/q$，使 $Q<q\le X/Q$，$|\theta-a/q|\le 2Q/(qX)$。在 (4) 中取 $y=H$；此时 $1+X|\theta-a/q|\le3$，而 $\varphi(q)\gg\sqrt q$。于是

$$
 \sup_{\theta\in\mathfrak m}|F_H(\theta)|
 \ll XQ^{-1/2}L^2 .
$$

记 $C_y(N)=\int_{\mathfrak m}F_yF_H e(-N\theta)\,d\theta$。由 Bessel 不等式和 $\int_0^1 |F_y|^2=\sum_{m\le y}\Lambda(m)^2\ll XL$，得到对每个固定截点 $y$ 的估计

$$
 \boxed{\quad
 \sum_{X\le N\le 2X}|C_y(N)|^2
 \le \int_{\mathfrak m}|F_y F_H|^2
 \ll X^3L^5/Q .\quad} \tag{7}
$$

式 (7) 中的和包括所有整数。这是证明中首次对目标整数取平均的地方。把它直接替换成对每个系数的 $o(X)$ 估计，会丢失原有的量词。



## 从有限网格到最大奇异值

<small>原稿第 4 页</small>

取 $K=\lceil L^{a_0}\rceil$、$y_j=Hj/K$（$0\le j\le K$）。将某个 $|C_{y_j}(N)|>XL^{-a_0}$ 的整数列入例外集 $E_X$。式 (7) 及 Chebyshev 不等式给出

$$
 |E_X|\ \ll\ (K+1)\frac{X^3L^5/Q}{X^2L^{-2a_0}}
 \ll_A X^{2/3} L^{5a_0+15}
 \ll_{A,\varepsilon} X^{2/3+\varepsilon}. \tag{8}
$$

对 $N\notin E_X$ 的偶数，在每个网格点有 $|R_{y_j}(N)-S_N\min(y_j,N)|\ll_A XL^{-a_0}$。因 $R_y(N)$ 单调，主项在相邻节点间的增量至多 $S_N H/K$，此界可推广至所有 $y$，误差为 $O_A(S_N X L^{-a_0})$。这里用到偶数的 $S_N\ge2C_2>0$。

还须处理算子中的互素条件。若 $(m,N)>1$ 且 $\Lambda(m)\ne0$，则 $m$ 是 $N$ 的某个素因子的幂。对每个 $p\mid N$，这些幂上的 $\Lambda$ 总和不超过 $L$，且 $\Lambda(N-m)\le L$。所有被删项目的总权故至多 $\omega(N)L^2=O(L^3)$。取 $y=xN$ 和 $y=N/3$ 两次相减、再除以 $N$，就得到在 $I$ 上一致的界

$$
  \sup_{x\in I}|S_N(x-1/3)-\nu_N((1/3,x])|
  \ll_A S_N L^{-a_0}\qquad (N\notin E_X).
$$

由 (3) 作 Stieltjes 分部积分，对 $f(u)\overline{g(1-u)}$ 求导，再用一维 Sobolev 不等式，便知 $\|B_N\|$ 被上述上确界的绝对常数倍控制。因 $a_0=A+2$，充分大 $X$ 时可吸收常数。这证明了 (1)。

**仍待证明的单整数抵消。** 同一网格论证保留小弧系数后，还给出对每个偶数成立的归约

$$
 \frac{\|B_N\|}{S_N}\ll_A L^{-a_0}
 +\frac{\max_{0\le j\le K}|C_{y_j}(N)|}{X S_N}. \tag{9}
$$

因此，若某个充分大的 $N$ 满足 $\|B_N\|\ge cS_N$（固定 $c>0$），至少一个明确的小弧傅里叶系数必须达到 $\gg_{c,A} X S_N$。单个这种系数仍与 (7) 相容。若要沿这条途径排除所有大偶数的缺陷，还缺对 (9) 右端小弧项的逐偶数抵消。式 (1) 和 (9) 均针对平衡压缩 $B_N$。

### 文献与 Lean 核验

[1] J. Li、J. Liu，*A Conditional Proof of the Goldbach Conjecture*，§§5–7。[山东大学稿本](https://mrc.sdu.edu.cn/info/1018/2193.htm)　[2] R. C. Vaughan，*The Selberg Sieve*，哥德巴赫素数对上界。[讲义](https://personal.science.psu.edu/rcv4/571s25/Class571-04.pdf)  
[3] H. L. Montgomery、R. C. Vaughan，*Multiplicative Number Theory I*，定理 13.7。[原文](https://ndl.ethernet.edu.et/bitstream/123456789/23715/1/Hugh%20L.%20Montgomery.pdf)　[4] D. A. Goldston、J. Ziegler Hunts、T. Ngotiaoco，*The Tail of the Singular Series for the Prime Pair and Goldbach Problems*。[预印本](https://arxiv.org/abs/1409.2151)

配套 Lean 文件验证紧测试类上的一致化、单调截点的网格误差和有限二阶矩对例外集大小的上界。GRH 特征和、主弧近似、Bessel 估计及其综合为本文的解析证明。
