# 哥德巴赫算子的平方根例外集

<small>原稿第 1 页</small>

设 $X\le N\le 2X$，$N$ 为偶数，$H=2X$，$L=\log H$。记 $I=(a,b)=(1/3,2/3)$，$\ell=b-a$，$S_N=\mathfrak S(N)$ 为二元哥德巴赫奇异级数。$B_N$ 是李–刘算子 $T_N=P_N-D_N-K_N$ 在 $I$ 的 Mellin 测试向量子空间 $V_N$ 上的正交压缩。下文假设全体 Dirichlet $L$ 函数的 GRH。

**定理。** 对充分大的 $X$，有

$$
 \boxed{\ \sum_{\substack{X\le N\le2X\\2\mid N}}\|B_N\|_{\mathrm{HS}}^2
       \ll X^{1/2}L^4.\ } \tag{1}
$$

因 $S_N\ge 2C_2>0$（$C_2$ 为孪生素数常数）且 $\|B_N\|\le\|B_N\|_{\mathrm{HS}}$，对任意固定 $A>0$，范数超过 $S_N L^{-A}$ 的偶数至多有 $O_A(X^{1/2}L^{2A+4})$ 个。若以 $S_N X^{-\delta}$ 为阈值，则例外至多 $O(X^{1/2+2\delta}L^4)$ 个。当 $0<\delta<1/4$ 时，例外占比趋于零。对任一固定 $c_J>0$，固定比例缺陷 $\|B_N\|\ge c_JS_N$ 的个数为 $O_{c_J}(\sqrt X L^4)$。

**从测度到算子。** 设 $\Lambda$ 为冯·曼戈尔特函数，取有限实符号测度

$$
 \rho_N=S_N\,du-\frac1N\sum_{\substack{m/N\in I\\(m,N)=1}}
                 \Lambda(m)\Lambda(N-m)\,\delta_{m/N}.
$$

对任意有限实符号测度 $\sigma$，定义 $\mathcal B_N(\sigma)$ 的混合型为
$\langle\mathcal B_N(\sigma)v_g,v_f\rangle=\int_I f(u)\overline{g(1-u)}\,d\sigma(u)$。在 $I$ 上，奇特征正交性使 $P_N-D_N$ 留下 $m+n=N$ 的负项，$-K_N$ 的反射项给出 $S_N\,du$。故 $B_N=\mathcal B_N(\rho_N)$，见[前篇式 (3)](03-defect.md)。取 $\alpha=1/\log N$、$\beta=1/8$，Mellin 测试向量的精确范数为 [1, 命题 7.4；6, 式 (2)]

$$
 \|v_f\|^2=\frac1{2\pi}\int_I
 \frac{(Nu)^{2\alpha}}{1+(Nu)^{-2(\beta-\alpha)}}\,|f(u)/2-uf'(u)|^2\,du .
$$

分式在 $I$ 上一致地夹在两个正常数之间。分部积分给 $\int_I|f/2-uf'|^2=\int_I(u^2|f'|^2+3|f|^2/4)$，故 $\|v_f\|\asymp\|f'\|_2$，常数与 $N$ 无关。

记 $D_\sigma(u)=\sigma((a,u])$。对任意实常数 $c$，

$$
 \|\mathcal B_N(\sigma)\|_{\mathrm{HS}}^2
      \ll \int_I |D_\sigma(u)-c|^2\,du . \tag{2}
$$

**证明。** 赋予 $H_0^1(I)$ 导数范数。令 $W_N f=v_{\bar f}$，则 $W_N$ 是到 $V_N$ 的线性同构，且它与逆映射均一致有界。令 $A_\sigma$ 对应型 $\int f\bar g\,d\sigma$。反射 $\mathcal Rf(u)=f(1-u)$ 是酉算子，故 $W_N^*\mathcal B_N(\sigma)W_N=A_\sigma\mathcal R$。

由 $f(u)=\int_a^u f'(s)\,ds$，导数将 $H_0^1$ 等距地送到零均值的 $L^2(I)$。Fubini 给出 $A_\sigma$ 在此子空间上的压缩核 $\sigma(I)-D_\sigma(\max(s,t))$，原子处左右极限的差只影响二维零测集。常数核在零均值空间上消失，而且压缩不会增大 HS 范数。最后用 $\iint_{I^2}|D_\sigma(\max(s,t))-c|^2\,ds\,dt=2\int_I (t-a)|D_\sigma(t)-c|^2dt$ 及 $\|W_N^{-1}\|\ll1$ 即得 (2)。



## 有理数附近的素数指数和

<small>原稿第 2 页</small>

写 $e(t)=\exp(2\pi it)$，$\mathbb T=\mathbb R/\mathbb Z$，对 $0\le y\le H$ 置

$$
 F_y(\theta)=\sum_{1\le m\le y}\Lambda(m)e(m\theta),\qquad
 V_y(\beta)=\int_0^y e(t\beta)\,dt,\qquad Q=\lfloor \sqrt H/L\rfloor .
$$

对模一的各既约分数 $h/q$、$q\le Q$，取区间 $|\theta-h/q|\le 1/(4qQ)$。它们互不相交，因为两个相异既约分数的距离至少为 $1/(qq')$。在上述区间上令 $J_y(h/q+\beta)=\mu(q)V_y(\beta)/\varphi(q)$，其余处令 $J_y=0$。共同分母使用相同弧宽，以便随后对分子精确求和。

对每个截点 $y$ 都有

$$
 \|F_y-J_y\|_\infty\ll H^{3/4}L^{3/2}. \tag{3}
$$

关键输入是 Friedlander–Goldston 式 (1.15)。在 GRH 下，对数素数权指数和扣除 $\mu(q)\varphi(q)^{-1}\sum_{m\le y}e(m\beta)$ 后，误差至多为常数乘 $\sqrt{qy}\log(2y)(\log(2y)+\sqrt{y|\beta|})$，此处只需 $q\le y$、$|\beta|\le q^{-2}$ 的情形。由素数权换成 $\Lambda$ 的误差为 $O(\sqrt H\,L^2)$。由等比级数公式，$|\beta|\le1/2$ 时 $\sum_{m\le y}e(m\beta)-V_y(\beta)=O(1)$，实截点取整也只损失 $O(1)$。[2]

在 $q\le Q$、$|\beta|\le1/(qQ)$ 上，总误差为

$$
 \ll \sqrt{QH}\,L^2+\frac{H}{\sqrt Q}L
 \ll H^{3/4}L^{3/2}.
$$

若 $y<q$，可直接用 $|F_y|+|V_y|\ll q$。在模型弧外，Dirichlet 逼近仍给出某个 $q\le Q$ 使 $|\beta|\le1/(qQ)$，而此时 $|\beta|\ge1/(4qQ)$。这个逼近分数的主项至多为 $O(qQ/\varphi(q))=O(Q^{3/2})$，已含在 (3) 内。由此验证 (3) 在整圆上有效。

Parseval 给出 $\|F_y\|_2^2=\sum_{m\le y}\Lambda(m)^2\ll HL$。对每个分母将 $\beta$ 积分延至实线，用 $\int_{\mathbb R}|V_y|^2=y$ 得
$\|J_y\|_2^2\le H\sum_{q\le Q}\mu(q)^2/\varphi(q)\ll HL$。末和的上界也由 Mertens 乘积给出。利用
$F_y F_H-J_yJ_H=(F_y-J_y)F_H+J_y(F_H-J_H)$，得到

$$
 \int_{\mathbb T}|F_y F_H-J_yJ_H|^2\,d\theta\ll H^{5/2}L^4 .
 \tag{4}
$$

这一步同时使用一致的指数和估计与一份 $L^2$ 范数。式 (4) 对 $y$ 一致，下一页先固定 $y$ 取傅里叶系数，再对 $y$ 积分。



## 从圆法的二阶矩到全部奇异值

<small>原稿第 3 页</small>

令 $c_q(n)=\sum_{h\bmod q}^{*}e(hn/q)$。以 $\widehat F(N)=\int_{\mathbb T}F(\theta)e(-N\theta)d\theta$ 为约定。模型乘积的第 $N$ 个系数为

$$
 \sum_{q\le Q}\frac{\mu(q)^2 c_q(N)}{\varphi(q)^2}
 \int_{|\beta|\le1/(4qQ)} V_y(\beta)V_H(\beta)e(-N\beta)\,d\beta .
$$

延至实线后，内部积分恰为 $\min(y,N)$，来自两个区间示性函数的卷积。每个积分的尾部为 $O(qQ)$，因为 $|V_y V_H|\ll|\beta|^{-2}$。对每个 $\eta>0$、每个 $1\le T\le H$、每个 $1\le N\le H$，有

$$
 \sum_{q\le T}\frac{q|c_q(N)|}{\varphi(q)^2}\ll_\eta H^\eta,\qquad
 \sum_{q>T}\frac{|c_q(N)|}{\varphi(q)^2}\ll_\eta H^\eta/T . \tag{5}
$$

实际上 $|c_q(N)|\le(q,N)\le\sum_{d\mid q,\,d\mid N}d$。对任意小的 $t>0$，用 $\varphi(q)^{-2}\ll_t q^{-2+t}$，写 $q=dr$。第一式每个 $d\mid N$ 贡献 $O_t(T^t)$。第二式在 $d\le T$ 与 $d>T$ 时每个 $d$ 均贡献 $O_t(T^{-1+t})$。再用 $\tau(N)\ll_t H^t$ 即得 (5)。偶数的完整 Ramanujan 级数等于 $S_N$。[3, 4]

记 $R_y(N)=\widehat{F_y F_H}(N)=\sum_{m+r=N,\ m\le y}\Lambda(m)\Lambda(r)$，求和仅取正整数。写 $E_N(y)=R_y(N)-S_N\min(y,N)$。由 (5)，模型系数与 $S_N\min(y,N)$ 相差 $O_\eta((Q+H/Q)H^\eta)$，对每个偶数都成立。固定 $\eta=1/8$，此项平方后在至多 $H$ 个整数上求和，只给 $O(H^{9/4}L^2)$。由 (4) 和 Bessel 不等式，

$$
 \sum_{\substack{X\le N\le2X\\2\mid N}} |E_N(y)|^2
 \ll X^{5/2}L^4 \qquad(0\le y\le H). \tag{6}
$$

若 $\Lambda(m)\ne0$ 且 $(m,N)>1$，则 $m$ 必为 $p\mid N$ 的幂，每个 $p$ 的 $\Lambda(m)$ 总和至多 $L$。恢复互素条件所删去的权重因此至多为 $\omega(N)L^2=O(L^3)$。因此
$D_{\rho_N}(u)=(E_N(aN)-E_N(Nu))/N+O(L^3/N)$。在 (2) 取 $c=E_N(aN)/N$，令 $y=Nu$，得到

$$
 \|B_N\|_{\mathrm{HS}}^2
 \ll N^{-3}\int_{aN}^{bN}|E_N(y)|^2dy+L^6/N^2. \tag{7}
$$

把各积分区间扩大到 $[0,H]$，交换求和与积分，再用 (6)。所得为 $O(X^{-3}H X^{5/2}L^4+L^6/X)$，即定理 (1)。这里直接估计 $\sum_j s_j(B_N)^2$。随 $N$ 移动的截点已在 (7) 中消去，因而没有网格点数的损失。



## 对每个偶数消去两个混合项

<small>原稿第 4 页</small>

取 $R=\lfloor H^{1/4}\rfloor$，定义显式的算术函数以及奇异级数的截断

$$
 P_R(m)=\sum_{q\le R}\frac{\mu(q)}{\varphi(q)}c_q(m),\qquad
 U_R(m)=\Lambda(m)-P_R(m),\qquad
 S_{N,R}=\sum_{q\le R}\frac{\mu(q)^2c_q(N)}{\varphi(q)^2}.
$$

**逐偶数公式。** 对每个 $X\le N\le2X$ 的偶数和每个整数 $0\le z<N$，

$$
 R_z(N)-z S_N
    =\sum_{1\le m\le z}U_R(m)U_R(N-m)
       +O_\varepsilon(X^{3/4+\varepsilon}). \tag{8}
$$

**第一步。** 对平方自由的 $q$，展开 $c_q(N-m)=\sum_{d\mid(q,N-m)}d\mu(q/d)$。若 $(d,N)=1$，GRH 给 $\sum_{m\le z,\,m\equiv N\bmod d}\Lambda(m)=z/\varphi(d)+O(\sqrt H L^2)$。若 $(d,N)>1$，对应总权为 $O(L)$，因为这些整数全都含同一个固定素因子。由乘法性或逐素因子计算，

$$
 \sum_{\substack{d\mid q\\(d,N)=1}}\frac{d\,\mu(q/d)}{\varphi(d)}
 =\frac{\mu(q)c_q(N)}{\varphi(q)} .
$$

故 $\sum_{m\le z}\Lambda(m)P_R(N-m)=z S_{N,R}+O_\varepsilon(H^{1/2+\varepsilon}R)$。误差中使用了 $\sum_{q\le R}\sigma_1(q)/\varphi(q)\ll_\varepsilon R H^\varepsilon$，$\sigma_1(q)=\sum_{d\mid q}d$。换元 $r=N-m$ 并作两个前缀之差，对 $\sum_{m\le z}P_R(m)\Lambda(N-m)$ 得到相同的主项和误差。[3, 推论 13.8]

**第二步。** $c_q(m)c_r(N-m)$ 在一个公周期上的平均是 $\mathbf1_{q=r}c_q(N)$。展开成加性特征后，只有两个相等的既约频率贡献。对不满整周期的区间仍有精确误差控制。展开为 $d\mid m,\ e\mid N-m$ 两个条件，中国剩余定理给每一对相容条件的计数为 $z/[d,e]+O(1)$，其中 $[d,e]$ 是最小公倍数。因而未加权前缀相对其周期平均乘 $z$ 的误差至多为 $\sigma_1(q)\sigma_1(r)$。求和得

$$
 \sum_{m\le z}P_R(m)P_R(N-m)=z S_{N,R}+O_\varepsilon(R^2 H^\varepsilon).
$$

展开 $U_R(m)U_R(N-m)$ 后，两份混合主项减去一份纯模型主项，留下 $z S_{N,R}$。用 (5) 补上尾部，误差合计为 $O_\varepsilon(H^\varepsilon(\sqrt H R+R^2+H/R))$。代入 $R$ 即证 (8)。

令 $\mathcal U_{N,R}=\mathcal B_N(N^{-1}\sum_{m/N\in I}U_R(m)U_R(N-m)\delta_{m/N})$。由 (8) 在区间两端作差、恢复互素条件并应用 (2)，对每个偶数均有

$$
 \boxed{\ \|B_N+\mathcal U_{N,R}\|_{\mathrm{HS}}
              \ll_\varepsilon X^{-1/4+\varepsilon}.\ } \tag{9}
$$



## 排除逐点缺陷的等价算术条件

<small>原稿第 5 页</small>

将第 4 页的有符号余项累加到平衡区间内的截点。定义

$$
 C_{N,R}(u)=\frac1N\sum_{aN<m\le Nu} U_R(m)U_R(N-m),\qquad
 \overline C_{N,R}=\frac1\ell\int_I C_{N,R}(u)\,du .
$$

**定理。** 沿任一趋于无穷的偶数序列，取 $X\le N\le 2X$ 和 $R=\lfloor(2X)^{1/4}\rfloor$（特别可取 $X=N$）。沿这条序列有

$$
 \boxed{\quad \frac{\|B_N\|}{S_N}\longrightarrow0
 \quad\Longleftrightarrow\quad
 \frac{1}{S_N^2}\int_I |C_{N,R}(u)-\overline C_{N,R}|^2\,du\longrightarrow0.\quad}
 \tag{10}
$$

右侧对每个 $N$ 只取一次截点积分。它允许个别截点上的相关和偏大，也消去了与截点无关的偏差。

**证明。** 令 $D=D_{\rho_N}$，$d=\inf_c\|D-c\|_{L^2(I)}$，$M=\|B_N\|$。由 (2)，$M\ll d$。Selberg 上界筛给 $\#\{p+q=N\}\ll NS_N/(\log N)^2$，高次素数幂的归一化权重至多为 $O(N^{-1/2}L^3)$。因此 $\|\rho_N\|_{\mathrm{TV}}\ll S_N$，特别有 $|D|\ll S_N$。[5]

为证相反方向的定量界，取 $0<\eta\le\ell/4$，令 $J_\eta=(a+\eta,b-\eta)$，$c_\eta$ 为 $D$ 在 $J_\eta$ 上的平均。取实函数 $g\in H_0^1(I)$ 在 $J_\eta$ 上恒为一，在两端长度为 $\eta$ 的区间上线性降至零，故 $\|g'\|_2=\sqrt{2/\eta}$。取 $f$ 为 $D-c_\eta$ 在 $J_\eta$ 上从左端点起的原函数，并向两侧延零。因 $f$ 在两端均为零，且 $J_\eta$ 关于反射对称，分部积分给出

$$
 |\langle B_N v_g,v_f\rangle|
 =\left|\int_I f\,d\rho_N\right|
 =\|D-c_\eta\|_{L^2(J_\eta)}^2 .
$$

用 $\|v_f\|\ll\|f'\|_2$ 与 $\|v_g\|\ll\eta^{-1/2}$，得 $\|D-c_\eta\|_{L^2(J_\eta)}\ll M/\sqrt\eta$。余下两个区间的总长为 $2\eta$，且 $|D-c_\eta|\ll S_N$。所以

$$
 d^2\ll M^2/\eta+\eta S_N^2,\qquad
 \frac{d^2}{S_N^2}\ll\frac{M}{S_N}\ll\frac d{S_N}. \tag{11}
$$

第二式在 $0<M/S_N\le\ell/4$ 时取 $\eta=M/S_N$。若 $M/S_N>\ell/4$，直接用 $d\ll S_N$，而 $M=0$ 时令 $\eta\downarrow0$。

最后，在 (8) 取 $z=\lfloor Nu\rfloor$ 与 $\lfloor Na\rfloor$ 后相减。除以 $N$，补回互素条件和取整误差，得到 $\sup_{u\in I}|D(u)+C_{N,R}(u)|\ll_\varepsilon X^{-1/4+\varepsilon}$。到常函数子空间的 $L^2$ 距离是 1-Lipschitz，且 $C_{N,R}$ 的最佳常数为其平均。由 (11) 及 $S_N\gg1$ 即得 (10)。逐个偶数证明右侧趋于零，仍是未解决的步骤。



## 无素数对时的缺陷与直接估计的代价

<small>原稿第 6 页</small>

由 (9)，对任意固定 $c>0$，若充分大的偶数满足 $\|B_N\|\ge c S_N$，就有 $\|\mathcal U_{N,R}\|\ge c S_N/2$。这把持续的缺陷归结到有符号乘积 $U_R(m)U_R(N-m)$。式 (10) 精确描述排除这种缺陷需要的抵消。

**逐点的非负判据。** 第 1 页的导数空间有 Dirichlet Green 函数

$$
 G(u,v)=\frac{(\min(u,v)-a)(b-\max(u,v))}{b-a}.
$$

令 $\mathcal E_N=\iint_{I^2}G(u,v)^2d\rho_N(u)d\rho_N(v)$。对每个 $N$，再生核向量 $g_u=G(u,\cdot)$ 满足 $\langle g_u,g_v\rangle=G(u,v)$，且 $A_{\rho_N}=\int g_u\otimes g_u\,d\rho_N(u)$。故 $\mathcal E_N=\|A_{\rho_N}\|_{\mathrm{HS}}^2\ge0$。同时
$\|A_{\rho_N}\|_1\le\int G(u,u)\,d|\rho_N|(u)\ll S_N$，其中总变差界来自 Selberg 上界筛和高次素数幂的平凡估计，如第 5 页所示。由 $\|A\|_{\mathrm{HS}}^2\le\|A\|\|A\|_1$ 以及 $\|A\|\le\|A\|_{\mathrm{HS}}$，有

$$
 \frac{\mathcal E_N}{S_N^2}\ll\frac{\|B_N\|}{S_N}
       \ll \frac{\sqrt{\mathcal E_N}}{S_N}. \tag{12}
$$

因此，沿任一偶数序列，排除固定比例缺陷等价于 $\mathcal E_N=o(S_N^2)$。若平衡区间中没有素数对，高次素数幂的归一化权重为 $O(N^{-1/2}L^3)$，沿这样的偶数趋于无穷时有 $\mathcal E_N/S_N^2=\iint_{I^2}G^2\,du\,dv+o(1)=\ell^4/90+o(1)$。

更局部地，给定非空开区间 $J\Subset I$，取非零实函数 $f\in C_c^\infty(J)$ 及 $g(u)=f(1-u)$。若没有 $p/N\in J$ 的素数表示 $N=p+q$，混合型就等于 $S_N\int f^2+O_f(N^{-1/2}L^3)$，从而 $\|B_N\|\gg_J S_N$。由 (1)，这样的偶数至多有 $O_J(\sqrt X L^4)$ 个。

**直接取绝对值的代价。** 在 (8) 对反射乘积用 Cauchy–Schwarz，会遇到 $\sum_{m/N\in I}U_R(m)^2$。其大小为 $(3/4+o(1))\ell N\log X$。确实，$\sum_{m/N\in I}\Lambda(m)^2=\ell N\log X+O(X)$ 可由 GRH 下的素数定理及分部求和得到。第 4 页两个模型计算改取反射中心为零，使用 $c_q(-m)=c_q(m)$，给出两个对角模型和 $\sum\Lambda P_R$ 与 $\sum P_R^2$ 的共同主项 $\ell N\sum_{q\le R}\mu(q)^2/\varphi(q)$，误差为 $O_\varepsilon(X^{3/4+\varepsilon})$。此和为 $\log R+O(1)$，因为其 Dirichlet 级数除以 $\zeta(1+s)$ 后，每个素因子为 $1+(p^{-s}-p^{-2s})/(p(p-1))$，在 $\Re s>-1/2$ 绝对收敛且在 $s=0$ 取值一，与调和和卷积即得。因 $S_N\ll\log\log N$，这个 Cauchy–Schwarz 界超过所需的尺度。逐个偶数的有符号抵消仍待证明。弱谱假设还要求整个 Hardy 空间上的算子 $T_N$ 满足带速率的范数界。

### 文献与核验

[1] J. Li、J. Liu，*A Conditional Proof of the Goldbach Conjecture*，[山东大学稿本](https://mrc.sdu.edu.cn/english/info/1018/1514.htm)。[2] J. B. Friedlander、D. A. Goldston，*Sums of Three or More Primes*，式 (1.15)、(2.7)，[Trans. AMS 349 (1997)](https://doi.org/10.1090/S0002-9947-97-01652-8)。  
[3] H. L. Montgomery、R. C. Vaughan，*Multiplicative Number Theory I*，[第 4、13 章](https://ndl.ethernet.edu.et/bitstream/123456789/23715/1/Hugh%20L.%20Montgomery.pdf)。[4] D. A. Goldston、J. Ziegler Hunts、T. Ngotiaoco，*The Tail of the Singular Series for the Prime Pair and Goldbach Problems*，[arXiv:1409.2151](https://arxiv.org/abs/1409.2151)。[5] R. C. Vaughan，*The Selberg Sieve*，[课程讲义](https://personal.science.psu.edu/rcv4/571s25/Class571-04.pdf)。[6] Yilin Liu，*Failure of the Li–Liu spectral hypothesis R under Dirichlet GRH*，[预印本 v1，§2](https://hexagonmath.org/pdf/2611.00788v1)。

Lean 4.19.0 已核验八条引理，涵盖完整周期的频率正交、混合项消去、整圆乘积的 $L^2$ 误差、截点换元、移动区间的积分求和、减均值的最优性与例外集计数。GRH 指数和、算子识别及主体定理采用上述解析证明。
