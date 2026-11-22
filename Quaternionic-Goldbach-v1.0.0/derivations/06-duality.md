# 哥德巴赫压缩算子的六阶矩与对偶

<small>原稿第 1 页</small>

取充分大的 $X$，记 $D_X=\{n\in[X,2X]:2\mid n\}$，$L=\log(2X)$，$I=(a,b)=(1/3,2/3)$，$\ell=b-a$。$B_n$ 为李嘉旻、刘建亚算子在平衡区间测试子空间 $V_n$ 上的正交压缩。沿用全体 Dirichlet $L$ 函数的 GRH 及前稿的混合型恒等式 [1, 2]。$S_n=\mathfrak S(n)$ 是二元哥德巴赫奇异级数。置

$$
 d_n=\frac{\|B_n\|}{S_n},\qquad
 \sigma_n=du-\frac{1}{nS_n}\!
   \sum_{\substack{m/n\in I\\(m,n)=1}}\!
    \Lambda(m)\Lambda(n-m)\,\delta_{m/n}.
$$

在 $H^1_0(I)$ 上取导数范数，记 $A_\sigma$ 为型 $\int f\bar g\,d\sigma$ 对应的算子，$E_n=\|A_{\sigma_n}\|_{\rm HS}^2$。前稿的同构给出 $d_n\ll E_n^{1/2}$，且 $\|B_n\|_{\rm HS}/S_n\asymp E_n^{1/2}$，常数与 $n$ 无关。下文的六阶矩是未取平均的 $\mathcal M_X=\sum_{n\in D_X}E_n^3$。

第 3 页把 $E_n$ 精确写成带 $20x^3(1-x)$ 概率权的截点误差平方积分，并给出可删去的两端尺度。

**六阶矩归约。** 第 7、8 页给出有限核和带符号六重积分 $R_{X,K,\delta}$。取 $T=X^{1/4}L^{-2}$，$K=\lceil8LT\rceil$，$\delta=T^{-2}$。有绝对常数 $C$ 使

$$
 \mathcal M_X\le C\bigl(\max(R_{X,K,\delta},0)+X^{-1/2}L^{12}\bigr),
 \qquad
 |R_{X,K,\delta}|\le C\bigl(\mathcal M_X+X^{-1/2}L^{12}\bigr).
 \tag{1}
$$

只须估计 $|k|\le K$ 的频率。保留的配置对每个 $i<j$ 都满足 $|u_i-u_j|>\delta$ 和 $|u_i+u_j-1|>\delta$。该归约已控制高频和近对角项，远离对角线的带符号相关仍待估计。

**对偶与单点缺陷。** 第 4、5 页分别给出六阶矩与真实算子范数的精确对偶式。对每个固定 $0<c\le1$，可以取与 $n,X$ 无关的 $O(c^{-2})$ 个有理频率。若 $d_n\ge c$，其中至少一个频率上的归一化显式素数权误差 $|F_n|\gg c$。这个结论允许检验只集中在一个偶数上。

**条件推论。** 如能证明 $R_{X,K,\delta}\ll X^{-1/2}L^{12}$，则由 (1) 得 $\max_{n\in D_X}d_n\ll X^{-1/12}L^2$，从而排除任何固定比例的压缩缺陷。本文未证明这个算术上界。



## Green 核决定频率权重

<small>原稿第 2 页</small>

Dirichlet Green 核为 $G(u,v)=(\min(u,v)-a)(b-\max(u,v))/\ell$。定义
$$
 g(u)=G(u,u)=\frac{(u-a)(b-u)}\ell,\qquad
 r(u)=\log\frac{u-a}{b-u},\qquad r'(u)=\frac1{g(u)} .
$$

在 $u\le v$ 和 $u\ge v$ 两个区域直接相除，得到精确恒等式
$$
 G(u,v)^2=g(u)g(v)e^{-|r(u)-r(v)|}. \tag{2}
$$
若 $G_u=G(u,\cdot)$，则 $A_\sigma=\int G_u\otimes G_u\,d\sigma(u)$。这是 Schatten 类中的积分，因为 $\|G_u\|_{H^1_0}^2=g(u)\le\ell/4$，$\sigma$ 全变差有限。取 Hilbert–Schmidt 内积，核即为 $|\langle G_u,G_v\rangle|^2=G(u,v)^2$。

令 $\tau_n=r_\#(g\sigma_n)$，$F_n(\xi)=\int e^{-i\xi r}\,d\tau_n(r)$，$d\pi(\xi)=d\xi/[\pi(1+\xi^2)]$。由 $\int e^{i\xi t}d\pi(\xi)=e^{-|t|}$ 和 Fubini 得
$$
 E_n=\iint_{I^2}G(u,v)^2\,d\sigma_n(u)d\sigma_n(v)
      =\int_{\mathbb R}|F_n(\xi)|^2\,d\pi(\xi). \tag{3}
$$
$\sigma_n$ 关于 $1/2$ 对称，故 $F_n$ 实且偶。指数核的实线傅里叶变换为 $1/(1+i\xi)+1/(1-i\xi)$。频率权 $d\pi$ 由此确定，保留了绿核能量中的全部交叉项。

**可用于圆法的算术权。** 对每个 $m$ 令 $x=3m-n$，$y=2n-3m$，则 $x,y>0$，$x+y=n$，$x\equiv y\pmod 3$。记 $\sum_m^*$ 为第 1 页带区间与互素条件的和。通过 $u=a+\ell t$ 积分，得到
$$
 \begin{aligned}
 F_n(\xi)
 &=\ell^2\mathrm B(2-i\xi,2+i\xi)\\[-2pt]
 &\quad-\frac1{3n^3 S_n}\sum_m^*
 \Lambda(m)\Lambda(n-m)\,xy\,e^{-i\xi\log(x/y)} .
 \end{aligned} \tag{4}
$$
这里 $g(m/n)=xy/(3n^2)$。连续项也等于 $\ell^2\pi\xi(1+\xi^2)/(6\sinh(\pi\xi))$，在零频率取连续值 $\ell^2/6$。该公式由 $\Gamma(2+it)=(1+it)\Gamma(1+it)$ 与 Euler 反射公式直接得到。



## 正面空间的精确六阶矩权重

<small>原稿第 3 页</small>

令 $s=u-a$。对每个 $0<x\le1$ 置
$$
 e_n(x)=\frac{3}{(\ell x)^3}\int_{(a,a+\ell x]}(v-a)^2\,d\sigma_n(v).
$$
在实际计算中，它等于 $1$ 减去截于 $m/n\le a+\ell x$ 的算术和；每项的权是 $3(m/n-a)^2\Lambda(m)\Lambda(n-m)/[(\ell x)^3 nS_n]$，求和仍取第 1 页的互素及平衡条件。直接在正面空间有
$$
 \boxed{\quad E_n=\frac{\ell^4}{90}\int_0^1 |e_n(x)|^2\,20x^3(1-x)\,dx .\quad}
$$
该概率权是 $\mathrm{Beta}(4,2)$ 密度。它给出的能量与第 2 页的频率平方和完全相等。

**证明。** 设 $H(s)=(\ell-s)^2/s^2$。对 $s,t\in(0,\ell)$ 有
$G(a+s,a+t)^2=(st/\ell)^2\min(H(s),H(t))$。以 $-H'(y)=2\ell(\ell-y)/y^3$ 将后一个最小值写成从 $\max(s,t)$ 到 $\ell$ 的积分。对两份 $\sigma_n$ 先积分得
$$
 E_n=\frac2\ell\int_0^\ell\frac{\ell-y}{y^3}
    \left|\int_{(a,a+y]}(v-a)^2\,d\sigma_n(v)\right|^2dy.
$$
Fubini 可用，因为换成全变差后的二重核 $G^2$ 有界。代入 $y=\ell x$ 即得公式。记 $d\beta=20x^3(1-x)dx$。对任一子区间 $J$，Hölder 给出
$(\int_J |e_n|^2d\beta)^3\le\beta(J)^2\int_J |e_n|^6d\beta$，故可按截点积分后求和。

对偶检验也可在同一坐标中构造。若 $h\in L^2(\beta)$，交换积分得到
$$
 \int_0^1 e_n(x)\overline{h(x)}\,d\beta(x)=\int_I Q_h(v)\,d\sigma_n(v),\quad
 Q_h(v)=\frac{60(v-a)^2}{\ell^3}\int_{(v-a)/\ell}^1(1-x)\overline{h(x)}dx .
$$
对 $n$ 再取 $\ell^{6/5}$ 单位球的上确界，乘以 $\ell^2/\sqrt{90}$ 即得 $\mathcal M_X^{1/6}$。该公式直接把截点检验转为素数对的权。

**两端可以删到什么尺度。** 置 $\varepsilon_0=L/\sqrt X$，第 6 页的局部质量给出 $|e_n(x)|\ll1+\varepsilon_0/x$。因此对 $\varepsilon_0\le h\le1/2$、$0<j\le1/2$，
$$
 \int_{(0,h)\cup(1-j,1)} |e_n|^2\,d\beta\ll h^4+j^2.
$$
取 $h=X^{-1/8}L$，$j=X^{-1/4}L^2$ 时，两端所占能量的立方，对全部 $n$ 求和为 $O(X^{-1/2}L^{12})$。从而目标六阶矩上界等价于在 $[h,1-j]$ 上证明同尺度的能量立方和上界。两端的不同截点来自概率权在两端的不同零点阶数。



## 六阶矩的最优对偶函数

<small>原稿第 4 页</small>

由 (3)，$\mathcal M_X^{1/6}$ 是向量 $(F_n)_{n\in D_X}$ 在 $\ell^6(L^2(\pi))$ 中的范数。因此
$$
 \mathcal M_X^{1/6}
 =\sup_{\sum_n\|h_n\|_2^{6/5}\le1}
 \left|\sum_n\int F_n\overline{h_n}\,d\pi\right|
 =\sup_{\sum_n\|h_n\|_2^{6/5}\le1}
 \left|\sum_n\int_I \Psi_{h_n}\,d\sigma_n\right|, \tag{5}
$$
其中 $\Psi_h(u)=g(u)\int e^{-i\xi r(u)}\overline{h(\xi)}\,d\pi(\xi)$。当 $\mathcal M_X>0$ 时，上确界由
$$ h_n=\mathcal M_X^{-5/6}E_n^2F_n $$
达到，因为 $\sum_n\|h_n\|_2^{6/5}=1$。全零时任取零检验即可。对实 Hilbert 空间，也可把 (5) 写成
$\sum\|z_n\|^6=\max_q\sum_n(6\|q_n\|^4\langle z_n,q_n\rangle-5\|q_n\|^6)$，最大值由 $q=z$ 取得。

**区间上的对偶范数。** 写 $\Psi(u)=g(u)f(r(u))$。由 Plancherel，其检验范数为
$$
 \|\Psi\|_*^2=\frac12\int_{\mathbb R}(|f'|^2+|f|^2)\,dr
 =\int_a^b\left(\frac{|\Psi'|^2}{2g}+\frac{|\Psi|^2}{\ell g^2}\right)du. \tag{6}
$$
第二式先对紧支撑光滑函数分部积分，使用 $g''=-2/\ell$ 和 $1-(g')^2=4g/\ell$，再取完备化。再生核是 $e^{-|r-s|}$，因为它满足 $(1-\partial_r^2)e^{-|r-s|}=2\delta_s$。对给定 $\tau_n$ 的 Riesz 代表为 $f_n^*(r)=\int e^{-|r-s|}\,d\tau_n(s)$，区间代表即 $\int G(u,v)^2d\sigma_n(v)$。

记 $u_m=m/n$，$w_m=\Lambda(m)\Lambda(n-m)/(nS_n)$，只对允许的 $m$ 求和。实际 $n$ 的最优检验在区间上也可直接计算。其未归一化形式为
$$
 \begin{aligned}
 \Psi_n^*(u)={}&\frac\ell3 g(u)^2-
 \frac{(b-u)^2}{\ell^2}\sum_{u_m\le u}w_m(u_m-a)^2\\
 &-\frac{(u-a)^2}{\ell^2}\sum_{u_m>u}w_m(b-u_m)^2 .
 \end{aligned}
$$
当 $E_n>0$ 时，把它除以 $\sqrt{E_n}$ 即得达到单个能量对偶范数的单位检验。

**无平衡素数对时的最优权重。** 对模型 $\sigma=du$，分段直接积分得
$$
 \int_I G(u,v)^2\,dv=\frac\ell3 g(u)^2,\qquad
 E(du)=\frac{\ell^4}{90}.
$$
故单位范数最优检验为 $\sqrt{10}\,g^2/\ell$。若没有平衡素数对，$\sigma_n$ 与 $du$ 的全变差距离是 $O(L/\sqrt X)$（第 6 页），于是 $E_n=\ell^4/90+O(L/\sqrt X)$。这一权重来自精确最大化。



## 真实算子范数与单个偶数

<small>原稿第 5 页</small>

沿用 Mellin 测试向量 $v_f$，其范数满足 $\|v_f\|\asymp\|f'\|_2$。对 $f,h\in H_0^1(I)$，$S_n^{-1}\langle B_n v_h,v_f\rangle=\int f(u)\overline{h(1-u)}d\sigma_n(u)$。令 $W_nf=v_{\bar f}$，$\mathcal R f(u)=f(1-u)$，则 $S_n^{-1}W_n^*B_nW_n=A_{\sigma_n}\mathcal R$。反射酉，$W_n$ 及其逆一致有界，因此第 1 页的范数比较成立。保留原始范数得
$$
 \Big(\sum_{n\in D_X} d_n^6\Big)^{1/6}
 =
 \sup_{\sum_n(\|v_{f_n}\|\|v_{h_n}\|)^{6/5}\le1}
 \left|\sum_n\int_I f_n(u)\overline{h_n(1-u)}\,d\sigma_n(u)\right|. \tag{7}
$$
右端保留每个 $n$ 的原始 Hilbert 范数。上界由算子范数和 Hölder 给出。反向取单位左右奇异向量，调整相位，再令每项的范数乘积为 $d_n^5/(\sum_jd_j^6)^{5/6}$。压缩紧性保证非零奇异值对应向量存在；也可取逼近最大值的向量。若所有 $d_n=0$，两边直接为零。取仅在 $n_0$ 非零的检验即可恢复 $d_{n_0}$。

**固定阈值只需有限个频率。** 对每个 $0<c\le1$ 有有理数集 $Q_c\subset[0,C/c]$，$\#Q_c\le Cc^{-2}$，且对充分大的所有偶数 $n$，
$$ d_n\ge c\quad\Longrightarrow\quad\max_{q\in Q_c}|F_n(q)|\ge c/C . \tag{8}$$
事实上 $E_n\gg c^2$。在第 7 页的 (10) 中取 $T=C_0/c$，选大常数使高频能量小于 $E_n/4$。所有离散权之和有界，故某个 $|\xi_k|\ll 1/c$ 满足 $|F_n(\xi_k)|\gg c$。又 $|F_n'|\le\sup_I(g|r|)\|\sigma_n\|_{\rm TV}\ll1$。在正半轴取步长介于 $c/C_1$ 和 $2c/C_1$ 的有理网格，利用偶性并取 $C_1$ 充分大即得 (8)。

**反向检验。** 取关于 $1/2$ 对称的截断 $\chi_\epsilon$，端点距离 $\le\epsilon$ 取零，$\ge2\epsilon$ 取一，中间线性。令 $f=\chi_\epsilon\sqrt g\,e^{-i\xi r/2}$。则 $f(u)\overline{f(1-u)}=\chi_\epsilon^2g e^{-i\xi r}$，且 $\|v_f\|^2\ll(1+\xi^2)\log(2/\epsilon)$，由 $r'=1/g$ 积分即得。端部损失 $\ll\epsilon\|\sigma_n\|_{\rm TV}$。于是
$$
 |F_n(\xi)|\ll\epsilon+(1+\xi^2)\log(2/\epsilon)\,d_n
 \qquad(0<\epsilon<\ell/8). \tag{9}
$$
(8)、(9) 给出的充要条件是沿偶数 $n\to\infty$ 有 $d_n\to0$，当且仅当每个固定非负有理数 $q$ 都满足 $F_n(q)\to0$。



## 短区间筛给出局部质量上界

<small>原稿第 6 页</small>

写 $C_2=\prod_{p>2}(1-1/(p-1)^2)$。偶数的奇异级数为
$S_n=2C_2\prod_{p\mid n,\ p>2}(p-1)/(p-2)\ge2C_2$。以下估计仅用上界筛。任取长度 $H$ 的整数区间，$X^{1/3}\le H\le 2X$，其中落在 $nI$ 且 $m,n-m$ 同为素数的 $m$ 的个数满足
$$ \#\{m\}\ll HS_n/(\log H)^2. $$

**筛的余项。** 对每个素数筛掉 $m\equiv0,n\pmod p$ 的剩余类。类数 $\rho(p)$ 在 $p\mid n$ 时为 $1$，否则为 $2$。对无平方因子 $d$，中国剩余定理在任一区间给出 $H\rho(d)/d+O(\rho(d))$。取 $z=H^{1/8}$，平衡区间内两个素数均超过 $z$。Selberg 上界筛给出主项 $H/G(z)$，其中
$$
 G(z)=\sum_{d\le z}\mu(d)^2\prod_{p\mid d}\frac{\rho(p)}{p-\rho(p)} .
$$
筛权满足 $|\lambda_d|\le1$。误差 $\ll\sum_{d,e\le z}2^{\omega([d,e])}\ll z^2(1+\log z)^2$，用到了 $2^{\omega(d)}\le\sum_{h\mid d}1$。标准筛不等式及二元哥德巴赫的局部类数见 [3]。

**对 $n$ 一致的分母。** 取 $Y=z^{1/8}$。将 $p\le Y$ 的欧拉乘积以每个因子的总质量归一化，得到独立选取素数的分布，选取概率为 $\rho(p)/p$。于是 $\mathbb E\log d\le2\sum_{p\le Y}(\log p)/p\le2\log Y+O(1)$，故 $d\le z$ 的项至少占乘积一半。Mertens 乘积及上述 $S_n$ 的公式给出
$$
 G(z)\gg\prod_{p\le Y}(1-\rho(p)/p)^{-1}
     \gg (\log Y)^2/S_n .
$$
末式也可逐个素因子检验，$p\nmid n$ 的尾部损失由 $C_2>0$ 控制，删去 $p\mid n$ 的奇异级数因子只会减小分母。这样得到所需区间筛界。

**局部质量。** 高次素数幂的归一化总权 $\ll L/\sqrt X$，因为 $\sum_{p^j\le2X,\,j\ge2}\log p\ll\sqrt X$，另一个 $\Lambda$ 至多为 $L$。若 $L/\sqrt X\le d\le1$，$J\subset I$ 的长度至多 $2d$，将短区间补足至长度 $\asymp nd$，上面的筛界乘 $L^2/(nS_n)$ 即得
$$ |\sigma_n|(J)\ll d,\qquad \|\sigma_n\|_{\rm TV}\ll1 . $$
补足后 $\log(nd)\asymp L$。反射 $u\mapsto 1-u$ 保持该估计。



## 高频尾部的逐点估计

<small>原稿第 7 页</small>

取 $P=8L$，$\xi_k=2\pi k/P$，$w_k=2/[P(1+\xi_k^2)]$。指数核的周期化为
$K_P(s)=\sum_{j\in\mathbb Z}e^{-|s+jP|}=\sum_{k\in\mathbb Z} w_k e^{i\xi_k s}$。
傅里叶系数由实线积分直接求出，且 $\sum_k w_k=\coth(P/2)\ll1$。对 $1\le T\le X^{1/3}$，记 $K=\lceil PT\rceil$，则对每个 $n\in D_X$ 有
$$
 \begin{aligned}
 E_n&=\sum_{k\in\mathbb Z}w_k|F_n(\xi_k)|^2+O(X^{-4}),\\
 H_{n,K}&:=\sum_{|k|>K}w_k|F_n(\xi_k)|^2\ll T^{-2}.
 \end{aligned} \tag{10}
$$

**周期化误差。** 算术原子的 $|r|=|\log(x/y)|\le L$。连续测度变为 $g(u(r))^2dr$，其中 $g(u(r))=\ell/(4\cosh^2(r/2))$。截掉 $|r|>2L$ 的全变差为 $O(e^{-4L})$。余下双积分中 $|r-s|\le4L$，故 $|K_P(r-s)-e^{-|r-s|}|\ll e^{-4L}$。两核一致有界，放回连续尾部即得首式。

**正核估计。** 将 $\tau_n$ 降到周长 $P$ 的圆上。每个宽度 $1/T$ 的窗口内的全变差 $\ll1/T$。对原子部分，由 $du/dr=g\le\ell/4$，上一页的局部估计适用，且原子支撑长度 $2L<P$；对连续部分，将指数衰减的密度周期求和即得。

对整数 $J\ge K$，Fejér 核 $\mathcal F_D(t)=D^{-1}|\sum_{0\le h<D}e^{2\pi iht}|^2$ 在 $D=4J+1$ 时的傅里叶系数在 $|k|\le2J$ 上至少为 $1/2$。又 $\mathcal F_D(t)\ll D/(1+D^2\|t\|_{\mathbb R/\mathbb Z}^2)$。对任一圆上位置，用宽度 $P/J\le1/T$ 的邻接窗口向两侧求和，得到
$$
 \sum_{|k|\le2J}|F_n(\xi_k)|^2
 \le 2\iint\mathcal F_D((r-s)/P)\,d|\tau_n^P|(r)d|\tau_n^P|(s)
 \ll J/T .
$$
这里 $\tau_n^P$ 为降到圆上的测度，外层总变差有界。在 $J<|k|\le2J$ 上 $w_k\ll P/J^2$；按 $J=2^jK$ 求和即得 $H_{n,K}\ll P/(TK)\ll T^{-2}$。

写 $E_{n,K}=\sum_{|k|\le K}w_k|F_n(\xi_k)|^2$，$M_K=\sum_n E_{n,K}^3$。于是 $\sum_n H_{n,K}^3\ll XT^{-6}$，且由 (10) 和 $(s+t)^3\le4(s^3+t^3)$（$s,t\ge0$）可在 $\mathcal M_X$ 与 $M_K$ 之间转换，上界损失至多为绝对常数倍和加项 $O(XT^{-6}+X^{-11})$。



## 六重积分中近对角项的吸收

<small>原稿第 8 页</small>

置 $\Phi_K(u)=(\sqrt{w_k}g(u)e^{-i\xi_k r(u)})_{|k|\le K}$，$C_K(u,v)=\langle\Phi_K(u),\Phi_K(v)\rangle$。由于频率成对，$C_K$ 实且对称，也可用实的正弦、余弦坐标。$\|\Phi_K(u)\|\ll1$。记 $z_n=\int\Phi_Kd\sigma_n$，则 $\|z_n\|^2=E_{n,K}$。令
$$
 \begin{aligned}
 \mathcal F_\delta&=\{(u_1,\ldots,u_6)\in I^6:
    \min(|u_i-u_j|,|u_i+u_j-1|)>\delta\ \ (i<j)\},\\
 R_{X,K,\delta}&=\sum_{n\in D_X}\int_{\mathcal F_\delta}
    \prod_{j=1}^3 C_K(u_{2j-1},u_{2j})\,d\sigma_n^{\otimes6}.
 \end{aligned}
$$
全域 $I^6$ 上的同一积分恰等于 $M_K$。任取 $0<\eta<1$ 以及 $L/\sqrt X\le\delta\le\ell/20$。有
$$ \boxed{\ |M_K-R_{X,K,\delta}|\le\eta M_K+C_\eta X\delta^3.\ } \tag{11}$$

**证明。** 在六个顶点的 $15$ 条边上作容斥，每条坏边表示两种接近关系的并。给定一个含边的图，设 $s$ 个顶点孤立，$v=6-s\ge2$，其余顶点组成 $b_0\le v/2$ 个连通分量。

先对所有孤立顶点按带符号测度积分。每个这种顶点在核乘积中只出现一次，其特征向量由 $z_n$ 取代。若一个核的两个顶点都孤立，则贡献 $\|z_n\|^2$。用 Cauchy–Schwarz，余下核乘积的绝对值 $\ll\|z_n\|^s$。先做这一有符号积分，才能保留六阶矩的幂次。

对每个非平凡连通分量取一棵生成树。按全变差估计后可以丢弃额外的边。从叶子起积，每个受父节点限制的变量只落在两个长 $2\delta$ 的区间中，成本 $O(\delta)$；每个根的成本为 $O(1)$。故给定图的贡献
$$
 \ll E_{n,K}^{s/2}\delta^{v-b_0}
 \le E_{n,K}^{s/2}\delta^{(6-s)/2}.
$$
对 $s\le4$，Young 不等式将右端控制在 $\eta' E_{n,K}^3+C_{\eta'}\delta^3$。例如按 $\sqrt{E_{n,K}}\le A\sqrt\delta$ 与其补集分开，补集系数至多 $A^{-2}$。固定 $\eta'$ 使全部有限图的该系数之和小于 $\eta$。再对 $n$ 求和即得 (11)。式 (11) 保留误差 $\eta M_K$，留给左侧吸收。



## 剩余算术估计与核验范围

<small>原稿第 9 页</small>

由 (11) 取 $\eta=1/2$ 得 $M_K\le2\max(R_{X,K,\delta},0)+O(X\delta^3)$，并有 $R_{X,K,\delta}\ge-O(X\delta^3)$。结合 (10) 即得 (1)，因为
$$
 XT^{-6}=X\delta^3=X^{-1/2}L^{12},\qquad
 K\asymp X^{1/4}/L .
$$
因此只需远离对角项的**单侧上界**。在纯算术项中，每对位置满足 $\min(|m_i-m_j|,|m_i+m_j-n|)>n\delta\asymp\sqrt X\, L^4$。这个距离是在六阶矩目标容许的误差内取得的，未使用额外谱假设。

若调用前稿的 GRH 二阶矩界 $\sum_n\|B_n\|_{\rm HS}^2\ll\sqrt X L^4$，则由 $E_n\ll1$ 和 $S_n\gg1$ 这里只能直接推出 $\mathcal M_X\ll\sqrt X L^4$。与 (1) 所需的 $X^{-1/2}L^{12}$ 之间仍差一个 $X$ 的幂次（至多相差对数因子）。[2]

**必须利用中心化。** 将 $d\sigma_n^{\otimes6}$ 完全展开有 $2^6$ 项。只取全部均为 $du$ 的一项，其远离对角部分为
$$
 \#D_X\left(\frac{\ell^4}{90}\right)^3
      + O\bigl(X(\delta+T^{-2}+X^{-4})\bigr).
$$
事实上，未截频的单个能量在第 4 页已精确算出。周期化及截频误差照第 7 页取 $\sigma=du$；六个实变量的近对角区域体积 $O(\delta)$，且有限核一致有界。故该项单独的量级为 $X$。若逐项取绝对值再相加，这一个正项已经超过 (1) 所需尺度；所缺的抵消发生在素数、连续主项及其混合项之间。

**直接排查无素数对的偶数。** 还可用对称帐篷函数 $f(u)=\min(u-a,b-u)/\sqrt\ell$。有 $\|f'\|_2=1$，$f(u)^2=g(u)e^{-|r(u)|}$，且 $\int_I f^2du=\ell^2/12$。若无平衡素数对，(7) 的单点测试给出 $d_n\gg1$，因为余下的高次素数幂只贡献 $O(L/\sqrt X)$。此时 (4) 还给出 $F_n(0)=\ell^2/6+O(L/\sqrt X)$，所以单独证明零频率沿全部偶数趋零，就已经足够推出充分大偶数都有平衡素数对。式 (8) 则检验一般的算子缺陷。

### 文献与核验

[1] J. Li、J. Liu，*A Conditional Proof of the Goldbach Conjecture*。作者稿的条件为 GRH 加谱假设。[山东大学稿本与摘要](https://mrc.sdu.edu.cn/english/info/1018/1514.htm)  
[2] 本系列前稿给出压缩混合型及 $V_n$ 的一致范数等价。[平方根例外集，第 1 页](04-farey.md)  
[3] R. C. Vaughan，*Math 571, Chapter 4. The Selberg Sieve*，上界筛与例 5。[宾州州立大学讲义](https://personal.science.psu.edu/rcv4/571s25/Class571-04.pdf)

配套源文件经 Lean 4.19.0 与 mathlib v4.19.0 核验，内置公理检查覆盖 21 条定理，包括两种 Green 核分解、有限符号原子的截点平方积分、概率权及两端积分界、模型最优权与能量、有限特征能量、Hilbert 六阶矩的两种最大值公式、实 Hilbert 空间中可取到范数的算子的秩一对偶、有限森林估计及吸收不等式。连续傅里叶变换、短区间筛、Fejér 截断及六变量容斥的解析拼接在本文中以数学证明给出。
