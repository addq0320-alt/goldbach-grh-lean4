# 哥德巴赫六阶矩中的不相交零点

<small>原稿第 1 页</small>

设 $X$ 充分大，$L=\log(2X)$，沿用全体 Dirichlet $L$ 函数的 GRH 和前稿的圆法设置。两条素数和都绕分母一展开。在这个坐标里，两侧只比较 $\zeta$ 的零点纵坐标。本稿得到下列两个一致估计。

**匹配项。** 对任意可测集 $E\subset\mathfrak m$，令 $C_E(n)=\widehat{\mathbf1_E Z_{f_y}Z_g}(n)$，记
$$
 M_E(y)=\sum_{n\in2\mathbb Z}W(n/X)|C_E(n)|^6 .
$$
每个 $C_E$ 含两枚零点标签，将 $|C_E|^6=C_E^3\overline{C_E}^3$ 完全展开。$D_E(y)$ 表示前三个位置的六枚标签与后三个位置的六枚标签交集为空的子和。允许同侧重复，重数保留在各标签的系数中。则
$$
 \sup_{y,E}|M_E(y)-D_E(y)|\ll X^{11/2}L^{10}.                    \tag{1}
$$
这里 $D_E$ 是实数，交换正负两侧即取复共轭。式 (1) 也给恰好一对跨侧匹配的子和同阶界，见第 5 页。

**近原点频率。** 取 $T=X^{4/5}/L^2$，$E_0=\mathfrak m\cap\{X|\alpha|\le T\}$，$E_1=\mathfrak m\setminus E_0$，则
$$
 \sup_y M_{E_0}(y)\ll X^{11/2}L^9 .                                 \tag{2}
$$
再将纵坐标分入宽 $H=L$ 的高度段。记 $D^{\rm sep}_E$ 为只留任意两个不同频率位置的段号两两相差至少 $2$ 的带符号子和。经此分组及前稿的锐截点转移，原目标等价于
$$
 \boxed{\displaystyle\sup_{0\le y\le2X}D^{\rm sep}_{E_1}(y)
                     \ll X^{11/2}L^{12}.}                             \tag{3}
$$
余项里不同频率位置的任意两枚纵坐标相距大于 $L$。同一位置的两枚纵坐标仍可接近，每条固定光滑腿还可限制在相应的驻点高度。式 (3) 所需的带符号抵消和哥德巴赫谱假设仍待证明。



## 原算式、权与解析输入

<small>原稿第 2 页</small>

写 $e(t)=e^{2\pi it}$，取 $\alpha\in[-1/2,1/2)$，$\widehat H(n)=\int H(\alpha)e(-n\alpha)d\alpha$。从圆上删去以 $a/q$ 为中心、半宽 $L^4/X$ 的弧，其中 $(a,q)=1$，$q\le\lfloor X^{3/10}\rfloor$，余集记为 $\mathfrak m$。取固定实非负光滑窗 $W$，支撑于正轴紧区间，在 $[1,2]$ 为一。

前缀平滑宽为 $\delta=X^{4/5}$。取 $1<a<b<2$，固定光滑 $w_0$ 在 $t\le a$ 为零、在 $t\ge b$ 为一。令 $\rho$ 为支撑在 $(0,1)$ 的光滑概率密度，取
$$
 f(t)=f_y(t)=w_0(t)\int_0^1\rho(v)\mathbf1_{t\le y-\delta v}\,dv,
 \qquad g(t)=\eta(t/X).
$$
这里 $0\le w_0,\eta\le1$，$\eta$ 支撑于 $[a_0,b_0]\Subset(0,\infty)$，在 $[1/3,4/3]$ 为一，满足 $|\widehat\eta(\xi)|\ll e^{-c\sqrt{|\xi|}}$。两权变差一致有界。

令 $\gamma$ 遍历不同非平凡零点的纵坐标，包含两个符号，$m_\gamma$ 为重数。定义分母一的零点和
$$
 F_w(\gamma,\alpha)=\int_0^\infty w(t)t^{-1/2+i\gamma}e(\alpha t)dt,
 \qquad Z_w=-\sum_\gamma m_\gamma F_w(\gamma,\cdot).
$$
前稿关于真实素数和的 GRH 估计及分母一显式公式给出 [1]
$$
 \|Z_f\|_2+\|Z_g\|_2\ll\sqrt{XL},\qquad
 \|\mathbf1_{\mathfrak m}Z_g\|_\infty\ll X^{3/4}L^{3/2}.              \tag{4}
$$
前稿还证明原锐截点的 $\sup_y\operatorname{Re}\mathcal J_y\ll X^{11/2}L^{12}$ 等价于 $\sup_y M_{\mathfrak m}(y)\ll X^{11/2}L^{12}$。[1] 转移在完整带窗六阶范数上进行。因此以下从完整窗口展开，所有匹配条件都在这一表示内施加。



## 在零点纵坐标处取 Fourier 样本

<small>原稿第 3 页</small>

仅保留 $|\gamma|\le X^2$。对任意固定整数 $k$，在 $u=\log t$ 中分部积分有 $|F_w|\ll_k X^{1/2}(1+X)^k|\gamma|^{-k}$，一致于 $\alpha,y$。每个单位高度区间的零点数（计重）为 $O(\log(2+|\gamma|))$，由 Riemann–von Mangoldt 公式可得。[2] 因此截断尾在绝对和中为 $O_A(X^{-A})$。其余十一条腿的绝对和各至多为 $X$ 的固定次幂，可先加大 $k$。这个截断对带标签限制的子和也成立。

设 $A\in L^2(\mathbb R)$ 支撑于长 $\ell$ 的区间，$H(\xi)=\int A(u)e^{i\xi u}du$。对 $j=1,2$ 有
$$
 \sum_{|\gamma|\le X^2}m_\gamma^j|H(\gamma)|^2
             \ll L^j(1+\ell)\int |A(u)|^2du .                        \tag{5}
$$
平移 $A$ 使支撑含于 $[0,\ell]$，得到的 Fourier 变换模长相同。由实轴 Plancherel，$\|H'\|_2\le\ell\|H\|_2$。每个单位区间 $I$ 上，取 $|H|^2$ 至多等于其平均值的一点，再用微积分基本定理，得到
$$
 \sup_I |H|^2\le \int_I |H|^2+2\int_I|H H'|.
$$
对区间求和，右边 $\ll (1+\ell)\|A\|_2^2$。每个区间有 $\sum m_\gamma^j\ll L^j$，即证 (5)。这允许多个不同零点任意接近，也保留重零点。

对 $j=1$ 取 Hilbert 空间对偶。若 $J$ 长 $\ell$，$\Gamma\subset\{|\gamma|\le X^2\}$，则
$$
 \int_J\left|\sum_{\gamma\in\Gamma}m_\gamma b_\gamma e^{i\gamma u}\right|^2du
 \ll L(1+\ell)\sum_{\gamma\in\Gamma}m_\gamma|b_\gamma|^2 .           \tag{6}
$$
式 (5) 两次迭代也适用于支撑于矩形的二元 Fourier 变换。每个坐标付出自己的 $1+\ell$；光滑腿的对数支撑长度是 $O(1)$。



## 固定一个偶数后，每个位置的成本

<small>原稿第 4 页</small>

以下固定 $n$ 和可测集 $E\subset\mathfrak m$。若一个位置只固定权 $w$ 的标签，另一条腿 $h$ 的零点先按符号求和。令
$$
 \begin{aligned}
 V_h(x)&=\int_E Z_h(\alpha)e(-x\alpha)d\alpha,\\
 A_\gamma(n)&=-m_\gamma\int w(t)t^{-1/2+i\gamma}V_h(n-t)dt .
 \end{aligned}
$$
将 $\mathbf1_E Z_h$ 在圆的所选代表区间外延拓为零，实轴 Plancherel 和 (4) 给 $\|V_h\|_{L^2(\mathbb R)}^2\ll XL$。在 $u=\log t$ 下，被采样函数的平方积分恰为 $\int |w(t)V_h(n-t)|^2dt\ll XL$。式 (5) 取 $j=2$ 给
$$
 \sum_\gamma |A_\gamma(n)|^2\ll XL^4.                               \tag{7}
$$

若一个位置的两条腿都固定，置 $V_0(x)=\int_E e(-x\alpha)d\alpha$，于是 $\|V_0\|_2^2=|E|\le1$。双系数为
$$
 A_{\gamma,\tau}(n)=m_\gamma m_\tau\iint f(t)g(s)
             t^{-1/2+i\gamma}s^{-1/2+i\tau} V_0(n-t-s)\,dt\,ds .
$$
先按物理尺度 $S\le t<4S$ 切开前缀腿，$S$ 取 $4$ 的非负整数次幂。对每块，两个对数支撑长度都为 $O(1)$。固定 $t$，对 $s$ 积分至多付出 $\|V_0\|_2^2$，故
$$
 \iint_{S\le t<4S}|f(t)g(s)V_0(n-t-s)|^2dt\,ds\ll S .
$$
式 (5) 在两个坐标上迭代给分块的 $\ell^2_{\gamma,\tau}$ 范数 $\ll\sqrt S L^2$。用三角不等式与几何级数 $\sum_{S\le CX}\sqrt S\ll\sqrt X$ 合并，
$$
 \sum_{\gamma,\tau}|A_{\gamma,\tau}(n)|^2\ll XL^4.                  \tag{8}
$$
若相等条件迫使 $\gamma=\tau$，对角子集的平方和仍受 (8) 控制。同一纵坐标的两个重数因子已经算入。对负侧取复共轭不改变 (7)、(8)。这些界对所有 $n$ 一致。



## 跨侧匹配的总和

<small>原稿第 5 页</small>

正负两侧各有六枚标签，跨侧共有 $36$ 个可选相等条件。对“至少一条等式成立”作有限容斥。每个非空交集将部分标签识别为等价类，不同类之间可以继续取相同值。每个被识别的类至少出现在两个不同的频率位置，因为每条等式都有一端在正侧、一端在负侧。

设交集涉及 $s$ 个位置，$2\le s\le6$。未涉及的位置给 $C_E(n)$ 或其共轭。每个涉及的位置用 (7) 或 (8)，同类双腿用对角版本。对任一类，固定其余类，从出现它的数组中选两个作 Cauchy–Schwarz，其他数组用该变量的 $\ell^\infty\le\ell^2$。消去该类后部分 $\ell^2$ 范数仍是其余变量的数组，多个变量的平方和可交换。消去全部类，交集在固定 $n$ 的模至多
$$
 |C_E(n)|^{6-s}(\sqrt X\,L^{2})^s.                                \tag{9}
$$
式 (4) 与圆上 Parseval 给
$$
 \|C_E\|_{\ell^\infty}\ll XL,\qquad
 \sum_{n\in\mathbb Z}|C_E(n)|^2\ll X^{5/2}L^4 .
$$
$s=2$ 的四阶自由因子满足 $\sum W|C_E|^4\ll X^{9/2}L^6$。乘以 (9) 的 $XL^4$，恰得 $X^{11/2}L^{10}$。对 $s=3,4$，用同一二阶和与至多一个上确界，得到的 $X$ 指数分别为 $5,9/2$。对 $s=5$，窗口中 $\sum W|C_E|\ll X^{7/4}L^2$，合计指数 $17/4$。对 $s=6$ 直接数窗口长度，合计指数 $4$。后三种处理中的固定对数幂均可由严格的幂次余量吸收。

容斥项数为绝对常数，故得 (1)。任何仅由跨侧相等关系决定、且所有等式均为假时取零的指示函数，都是这些等式指标的多线性多项式，常数项为零。这也覆盖按重集计算恰好一对匹配的情形。



## 可一并移出的相邻高度段

<small>原稿第 6 页</small>

取 $1\le H\le L$，$b(\gamma)=\lfloor\gamma/H\rfloor$。在每条受约束的腿上，先将同一段 $b$ 内的零点按原符号相加。每段总重数 $\ll HL$。对任意 $H_A(\gamma)=\int A(u)e^{i\gamma u}du$，段内加权 Cauchy–Schwarz 及式 (5) 的 $j=1$ 版给
$$
 \sum_b\left|\sum_{b(\gamma)=b}m_\gamma H_A(\gamma)\right|^2
  \ll H L^2(1+\ell)\|A\|_2^2.                                       \tag{10}
$$
这一步保留了同段不同零点的复相位。式 (7) 的单段系数平方和至多 $XHL^4$，式 (8) 的双段系数平方和至多 $XH^2L^4$，由 (10) 在每个物理尺度上迭代，再按第 4 页合并即得。

在任意两个不同频率位置各选一条腿。若 $b_i-b_j\in\{-1,0,1\}$，称为同段或邻段。所有位置对共给 $4\binom62=60$ 对腿，覆盖同侧及跨侧。对 $60\times3$ 个具体等式作容斥。若一个交集的位移方程不相容，其贡献为零。否则每个连通分量可用一个整数 $b$ 参数化，各顶点取 $b+d_v$，$d_v$ 已固定。把数组在所有无标签的段号处延拓为零，整数平移保持平方和。若同一位置的两条腿属于同一分量，则 $(b+d_v,b+d_w)$ 构成无重复的斜对角，平方和受完整双段界控制。每个分量仍涉及至少两个不同位置。因此第 5 页的消元逐字适用，式 (9) 右端多出至多 $H^s$。

$s=2$ 给 $X^{11/2}H^2 L^{10}$；$s\ge3$ 的额外固定对数幂由 $X$ 的余量吸收。因此一致地有
$$
 |M_E-D_E^{\rm sep}|\ll X^{11/2}H^2L^{10},                          \tag{11}
$$
其中 $D_E^{\rm sep}$ 使用当前的段宽 $H$。取 $H=L$ 恰在目标量级。段号相差至少 $2$ 蕴含纵坐标间距严格大于 $H$。式 (11) 控制的是按指定网格删去的整个带符号子和；证明用到带位移等式的容斥。



## 将近原点的整段小弧移出

<small>原稿第 7 页</small>

在 $|\alpha|\le T/X$ 上取足够大的固定 $C_1$，每条腿先取 $|\gamma|\le C_1T$。由物理变量 $t$ 上的实轴 Plancherel，低零点部分在全部实频率上的平方积分等于
$$
 \int_{\log\operatorname{supp}w}
 |w(e^u)|^2\left|\sum_{|\gamma|\le C_1T}m_\gamma e^{i\gamma u}\right|^2du
 \ll T L^2(1+\ell_w).
$$
上界来自 (6) 和 $\sum_{|\gamma|\le C_1T}m_\gamma\ll TL$。其中 $\ell_f\ll L$，$\ell_g\ll1$。

超过 $C_1T$ 时，在 $x=t/X$ 中相位为 $\gamma\log x+2\pi X\alpha x$。对固定光滑腿分部积分 $k$ 次给 $|F_g|\ll_k\sqrt X(1+|\gamma|)^{-k}$，高零点尾在该区间上一致可忽略。前缀腿只用一致有界变差。一次分部积分所产生的因子为
$$
 \frac{\sqrt{x}}{i(\gamma+2\pi X\alpha x)} .
$$
在 $0<x<C$ 上其上界及总变差均为 $O(|\gamma|^{-1})$，从而 $|F_f|\ll\sqrt X/|\gamma|$。从 $C_1T$ 到 $X^2$ 对重数求和给 $O(\sqrt X L^2)$；更高处用第 3 页的截断。在长度 $2T/X$ 的区间上合并两段，得到
$$
 \|Z_f\|_{2,\mathrm{inner}}\ll\sqrt T L^2,\qquad
 \|Z_g\|_{2,\mathrm{inner}}\ll\sqrt T L .
$$
故 $\|C_{E_0}\|_\infty\ll TL^3$。用 (4) 的小弧上界及前缀的局部平方积分，有 $\sum_n|C_{E_0}(n)|^2\ll X^{3/2}T L^7$。于是
$$
 M_{E_0}\ll (TL^3)^4 X^{3/2}T L^7=X^{3/2}T^5L^{19}
                                  =X^{11/2}L^9 .
$$
三角不等式用于带权 $\ell^6$ 范数，给 $|M_{\mathfrak m}^{1/6}-M_{E_1}^{1/6}|\le M_{E_0}^{1/6}$。与 (11) 及前稿转移结合得到 (3)。



## 光滑腿的驻点和剩下的径向振荡

<small>原稿第 8 页</small>

在 $E_1$ 上，光滑腿相位导数为 $\gamma/x+2\pi X\alpha$。除
$$
 \gamma\alpha<0,\qquad
 \pi a_0 X|\alpha|\le|\gamma|\le4\pi b_0 X|\alpha|                  \tag{12}
$$
外，导数模 $\gg |\gamma|+X|\alpha|$，对固定振幅任意次分部积分。因 $X|\alpha|>T$，全部不满足 (12) 的光滑腿总质量可取 $O_A(X^{-A})$。将六个位置中的任一条这样消去，其余标签绝对求和也只有固定幂次的成本。先在与标签无关的 $E_1$ 证明 (11)，随后在 $D^{\rm sep}_{E_1}$ 内逐项施加 (12)。

在光滑局部块内，可以把系数窗口 Poisson 展开，并以 $z=n/X$ 对应的连续变量表示其 Fourier 核。令 $\epsilon_i=1$ 或 $-1$，每处的两个高度为 $t_i,s_i$；将本处的频率偏移写成 $B_i\lambda_i/X$，$u_i,v_i$ 为两个物理变量除以 $X$。联合实相位为下列逐位置和，加上线性项 $-\kappa z$：
$$
 \sum_i\epsilon_i\{t_i\log u_i+s_i\log v_i+
                       2\pi B_i\lambda_i(u_i+v_i-z)\}.
$$
这里 $\kappa$ 来自弧中心及半整数谐波；分母一且零谐波时 $\kappa=0$。换 $u_i=zx_i,\ v_i=zy_i,\ \lambda_i=\mu_i/z$，$z>0$，便得到精确的径向相位
$$
 T_* \log z-\kappa z,\qquad T_*=\sum_i\epsilon_i(t_i+s_i).
$$
其余相位与 $z$ 无关。每处横向三维 Hessian 的行列式绝对值为 $(2\pi B_i)^2|t_i/x_i^2+s_i/y_i^2|$，径向二阶导数为 $-T_*/z^2$。当 $T_*=\kappa=0$ 时径向的各阶导数全部消失。这个恒等式指出需要额外估计的近共振参数；它没有断言实际不相交零点之间发生精确加和关系。原锐小弧截边的振幅也不满足任意阶导数的一致估计。



## 十二个相隔很远的零点也能近共振

<small>原稿第 9 页</small>

取 $1\le H\le L$、$B=X^{9/10}$。在 $[B,2B]$ 内可取十二枚互异的正零点纵坐标，任两枚间距大于 $3H$，同时
$$
 \left|\sum_{i=1}^3(t_i+s_i)-\sum_{i=4}^6(t_i+s_i)\right|
                           \ll H^2/B .                            \tag{13}
$$
这是关于实际 $\zeta$ 零点的存在断言，只用宏观零点数与单位区间的上界。[2]

在 $[B,2B]$ 内先取三个长度均为 $B/10$、两两间隔至少 $B/10$ 的区间。每个区间内计重的零点数 $\gg B\log B$；任意长 $6H+2$ 的小区间含至多 $O(H\log B)$ 枚。贪心选择一个纵坐标并删去其 $3H$ 邻域，可得到 $N\gg B/H$ 枚两两相距大于 $3H$ 的纵坐标。

在每个大区间，将这 $N$ 枚数的所有无序双元素对按其和排序，共有 $\binom N2$ 个和，落在长 $O(B)$ 的区间内。两个不同的对，其和相距至多 $O(B/N^2)=O(H^2/B)$。这两对无法共用一个纵坐标，否则和之差就是两枚不同纵坐标的差，大于 $3H$。在三个区间各作一次选择，每次把一对放在正侧、另一对放在负侧，三项和之差给出 (13)。

这些标签满足 (11) 留下的分离条件，所有高度也都远大于 $T=X^{4/5}/L^2$。在零谐波的实相位中，当 $H=L$ 时径向二阶导数模可以小到 $O(L^2/B)$；若 $H=\sqrt L$ 则为 $O(L/B)$。因此，仅由零点互异、跨侧间距大和各腿高度大，无法推出一个随 $X$ 增长的径向曲率下界。式 (13) 并未估计这些配置在带权振荡积分中的净贡献；所需的仍是整个子和的带符号上界。



## 高阶一致性的反射检验

<small>原稿第 10 页</small>

取任意大素数 $p\equiv3\bmod4$，$c=(p+1)/2$，令 $a(x)=\chi_p(x-c)$，$\chi_p$ 为 Legendre 符号且 $\chi_p(0)=0$。在 $\mathbb F_p$ 上用概率归一化。Fouvry、Kowalski、Michel 关于驯分歧层的推论 1.6（亦见定理 1.1）给出，对固定 $d=3,4$ 有 [3]
$$
 \|a\|_{U^d}^{\,2^d}\ll_d p^{-1}.                                    \tag{14}
$$
初等一些的 $O_d(p^{-1/2})$ 上界也足够作检验。展开立方体平均后，根 $c-\omega\cdot h$ 两两相撞的 $h$ 至多落在 $O_d(1)$ 个超平面。其余 $h$ 对应次数 $2^d$ 的无重根多项式，固定 $h$ 的二次特征和由 Weil 界为 $O_d(\sqrt p)$。

另一方面，能直接算出每个输出处的反射卷积
$$
 \sum_{x\in\mathbb F_p}a(x)a(n-x)=
  \begin{cases}
    -(p-1), & n=2c,\\
    1,      & n\ne2c .
  \end{cases}                                                        \tag{15}
$$
在中心，$\chi_p(-1)=-1$ 使除 $x=c$ 以外的各项均为 $-1$。离开中心，取 $h=n-2c\ne0$，有 $\sum_z\chi_p(z)\chi_p(z-h)=-1$。因为 $z\mapsto z/(z-h)$ 将 $z\ne h$ 双射至去掉 $1$ 的域，且非零平方的特征为一。再乘 $\chi_p(-1)$ 即得。

于是未归一化的完整六阶矩恰为 $(p-1)^6+(p-1)$。若取 $A=\{x:a(x)=1\}$，则 $|A|=(p-1)/2$，且 $2c\notin A+A$。式 (14) 与 (15) 表明，即使立方体平均已达到这种尺度，固定输出的一次强反射仍可存在。Tao、Teräväinen 的定量定理处理减去局部模型后的 $\Lambda$ 的 Gowers 范数 [4]；将之用于这里还需利用素数特有的反射相关或窗口平均。



## 同一小弧窗口中的反例模型

<small>原稿第 11 页</small>

将上页 $a$ 周期延拓到整数，取 $X=p$、$y=p$、$n_0=p+1$；这是 $[X,2X]$ 内的偶数。对第 2 页的两种权，令 $P_{a,w}(\alpha)=\sum_m a(m)w(m)e(m\alpha)$。全圆系数精确等于
$$
 \widehat{P_{a,f}P_{a,g}}(n_0)=
       -\sum_{m\not\equiv c\bmod p} f(m)g(n_0-m).
$$
权非负，在 $p/3\le m\le p/2$ 上除至多一项外均给一，所以右边 $\le-c_1p$。另一方面，任意实 $\alpha$ 上有
$$
 \|P_{a,f}\|_\infty+\|P_{a,g}\|_\infty\ll\sqrt p\log(2p).
$$
模 $p$ 完成求和时，非零 Fourier 频率的 Gauss 和模长为 $\sqrt p$。区间的几何级数核在 $p$ 个等距点上模长之和为 $O(p\log(2p))$，由距最近整数的距离排序即可得。权的支撑分成固定个长度至多 $p$ 的区间，再按有界变差分部求和，得上界。

主弧测度 $\ll p^{-2/5}L^4$，故从全圆系数中剥离的主弧贡献至多 $O(p^{3/5}L^6)=o(p)$。原小弧和原窗口下仍有
$$
 \sum_{n\in2\mathbb Z}W(n/p)
  |\widehat{\mathbf1_{\mathfrak m}P_{a,f}P_{a,g}}(n)|^6\gg p^6.    \tag{16}
$$
用于比较，在大小 $N\asymp X$ 的有限群上，若卷积归一化为 $c(n)=N^{-1}\sum_x f(x)g(n-x)$，未取平均的目标对应 $\mathbb E_n|c(n)|^6\ll X^{-3/2}L^{12}$。仅一个大小 $\asymp1$ 的系数就贡献 $\asymp X^{-1}$。式 (16) 展示了这种损失在原小弧掩模下仍可发生。这里的模型权是二次特征；式 (16) 对真实 $\Lambda$ 没有给出下界。



## 有限域几何：确切的对角条件

<small>原稿第 12 页</small>

在奇素数域上取 $h_i\ne0$，令 $K_i(n)=p^{-1/2}S(k_i,(n-j_i)h_i;p)$，其中 $S(A,B;p)=\sum_{u\ne0}e_p(Au+B/u)$。在共同的 $n$ 上完整求和，正交性迫使 $v=(h_2/h_1)u$，故
$$
 \frac1p\sum_{n\bmod p}K_1(n)\overline{K_2(n)}
  =\frac1p S\!\left(k_1-k_2h_2/h_1,\ h_1(j_2-j_1);p\right).       \tag{17}
$$
若 $k_1h_1=k_2h_2$ 且 $j_1=j_2$，值为 $(p-1)/p$。若恰有一参数为零，值为 $-1/p$。其余情形由 Weil 界得模长至多 $2/\sqrt p$。[5] 因此是否保留常数项，可以在这个共同素模数模型中逐项判定。

四个互异奇素模数则有另一种精确计算。用 $p^{-1}\sum_n K(n)e_p(-rn)$ 归一化 Fourier 变换，频率 $r=0$ 时系数为零，其余处为
$$
            p^{-1/2} e_p(kh/r-rj).
$$
令 $M=p_1p_2p_3p_4$，各 $h_i$ 在本域非零。由中国剩余定理，乘积在模 $M$ 的 Fourier 系数 $b_r$ 满足 $b_r=0$ 若 $(r,M)>1$，其余处 $|b_r|=M^{-1/2}$。共轭某些因子不改变这个结论。对固定光滑紧支撑 $w$ 用 Poisson 求和，
$$
 \left|\sum_n w(n/X)\prod_{i=1}^4K_i(n)\right|
 \ll_{A,w}\frac X{\sqrt M}\sum_{\ell\ne0}(1+X|\ell|/M)^{-A}.
$$
当 $M\le X^{1-\delta}$ 时，可选 $A$ 获得任意固定幂次衰减。当 $M\asymp X^2$ 时，这一步只给 $O(\sqrt M)$。限偶数只需代入 $n=2m$。要把这项局部几何计算用于 (3)，仍需将不相交零点的权与这些有限域迹函数匹配，并保留短区间内的对偶相位。四个模数的数量本身不提供这种对应。



## 算子指标与六阶矩的区别

<small>原稿第 13 页</small>

在 $L^2(\mathbb T)$ 上取卷积算子 $K_G h=G*h$，其中 $G=\mathbf1_E Z_fZ_g$。令 $P_W$ 为 Fourier 乘子，符号为 $\mathbf1_{2\mid n}W(n/X)^{1/6}$。$H=P_WK_G$ 有限秩，Fourier 基将它对角化，给出原窗口的正迹公式
$$
               M_E=\operatorname{Tr}\big((H^*H)^3\big).              \tag{18}
$$
这是奇异值的六次幂和。Fredholm 指标只记录核与余核的维数差。取秩一正交投影 $P$，则 $I-tP$ 的指标恒为零。$t=1$ 时核与余核都为一维；其余实 $t$ 时算子可逆。同时 $\|tP\|_{\rm HS}=|t|$，六次迹为 $|t|^6$。因此只知道某个紧扰动的指标为零，不能给式 (18) 所需的量级。

**尚缺的算术估计。** 写 $a_i(n)=A_{\gamma_i,\tau_i}(n)$，取第 4 页在 $E_1$ 上的双系数。式 (3) 的左端对 $y$ 取上确界之前，具体为
$$
 \sum_{n\in2\mathbb Z}W(n/X)
 \sum_{\text{段号分离}}\!
 a_1(n)a_2(n)a_3(n)\,\overline{a_4(n)a_5(n)a_6(n)} .
$$
不同位置的任意两枚标签，段号相差至少二。同一位置内部仍有两枚自由标签；六条光滑腿都可再施加 (12)，误差为任意负幂。由 (11)，此和已有 $-O(X^{11/2}L^{12})$ 的下界。还缺对所有 $y$ 一致的上界，包括式 (13) 所示近共振配置的净贡献。

### 文献与核验

[1] [《哥德巴赫六阶矩的五模数项》](10-moduli.md)，第 11–12 页，式 (11)–(13)；[原圆法窗口](07-arcs.md)。

[2] [Riemann–von Mangoldt 公式](https://mathworld.wolfram.com/Riemann-vonMangoldtFormula.html)；[Bennett 等，零点计数](https://arxiv.org/abs/2005.02989)。

[3] Fouvry、Kowalski、Michel，[An inverse theorem for Gowers norms of trace functions](https://arxiv.org/abs/1211.3282)，推论 1.6、例 3.1，取一次多项式的二次特征。

[4] Tao、Teräväinen，[Quantitative bounds for Gowers uniformity](https://doi.org/10.4171/JEMS/1404)。[5] Harcos，[Weil’s bound for Kloosterman sums](https://users.renyi.hu/~gharcos/weil.pdf)。

配套 Lean 4 核验单位区间采样不等式、分块几何级数、有限数组求和、分段权重的均方、对角子集、带权矩插值、两处指数运算、完整二次特征反射卷积及径向相位分离。GRH 下的解析输入、连续采样与 (1)–(3) 的解析推导见正文。
