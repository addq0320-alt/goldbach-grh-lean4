# 分离零点和的两种大筛估计

<small>原稿第 1 页</small>

设 $L=\log(2X)$，$\ell=1+\log L$，$B_X=X^{11/2}L^{12}$，$X$ 充分大。沿用 Dirichlet GRH、等宽主弧与原实权。本稿的 $D_{\rm sep}(y)$ 专指《不相交零点》式 (3) 中 $D^{\rm sep}_{E_1}(y)$。它按 $\zeta$ 的零点纵坐标分段。同一频率位置有两枚纵坐标，不同位置的段号必须相差至少二。

**平衡算子的缺陷。** 对附件中的平衡压缩，固定 $c>0$，$\|B_N\|\ge cS_N$ 的偶数满足 $\sum S_N^2\ll_c X^{1/2}L^4$。若只求每个偶数都有平衡素数对，则只需证明三个指定长截点的 $(D_{\rm sep}(y))_+$ 的最大值为 $o(X^6)$。见式 (17)–(20)。

**一段完整的截点范围。** 置
$$
 Y_* = X^{4/5}L^{8/5}\ell^{-4/5}.
$$
对 $0\le y\le Y_*$ 有 $|D_{\rm sep}(y)|\ll B_X$。在全部 $[0,2X]$ 上，要证上界只需对间距 $Y_*$ 的网格点一致证明同一上界。与前稿的截点宽 $X^{4/5}$ 相比，对数改进来自真正同时筛 $m$ 和 $n-m$ 的素数对上界。

**每个截点上的一类分离项。** 将前三个位置的六个高度与后三个位置的六个高度按一个固定置换配对，记差为 $\delta_1,\dots,\delta_6$。取任意五个长度至多 $X^{3/10}$ 的指定区间，五个相应高度差分别落入其中，再要求 $|\sum_j\delta_j-\omega|\le1$。对原 $D_{\rm sep}(y)$ 中满足这些条件的项，逐项模长之和为 $O(B_X)$，一致于 $y$、区间位置及 $\omega$。

**全部标签的段宽。** 将 $L$ 换成与原网格对齐、大小 $\asymp X^{1/4}$ 的段宽，仍得到与原单侧目标等价的判据。这个结论通过吸收得到。只保留总高度近共振时，高度组的大筛还缺少对真实权重的抵消。下文量化其损失。



## 原和与可用的均方

<small>原稿第 2 页</small>

权 $f=f_y$ 是 $\mathbf1_{t\le y}$ 在上端以 $\delta=X^{4/5}$ 作的单侧光滑平均，在 $1<t<2$ 作固定下端修正。它满足 $|f|\le1$ 且支撑于 $1<t\le y$。$g(t)=\eta(t/X)$，$\eta$ 固定光滑、非负且支撑于紧正区间。$W\ge0$ 支撑在 $n\asymp X$ 的窗口，并在 $[1,2]$ 为一。以 $\alpha\in[-1/2,1/2)$ 表示圆的坐标，$e(t)=\exp(2\pi i t)$。小弧 $\mathfrak m$ 为分母 $q\le X^{3/10}$、半宽 $L^4/X$ 的既约主弧之补。置
$$
 T=X^{4/5}/L^2,\qquad E=E_1=\mathfrak m\cap\{X|\alpha|>T\}.
$$
对不同零点纵坐标 $\gamma$ 的重数记 $m_\gamma$，正负高度都取。写
$$
 F_w(\gamma,\alpha)=\int_0^\infty w(t)t^{-1/2+i\gamma}e(\alpha t)\,dt,\quad
 Z_w(\alpha)=-\sum_\gamma m_\gamma F_w(\gamma,\alpha).
$$
设置 $C(n)=\widehat{\mathbf1_E Z_f Z_g}(n)$，$M(y)=\sum'_n W(n/X)|C(n)|^6$，撇号表示偶数。$A_{\gamma\tau}(n)$ 是 $C(n)$ 中含两枚指定高度的项，包括重数。《不相交零点》式 (4)、(11) 及前稿转移给出 [1,2]
$$
 |M(y)-D_{\rm sep}(y)|\ll B_X,\qquad
 \|Z_f\|_2+\|Z_g\|_2\ll\sqrt{XL},\qquad
 \|\mathbf1_{\mathfrak m}Z_g\|_\infty\ll X^{3/4}L^{3/2}.       \tag{1}
$$
比较真实锐截点时，记 $P_y(\alpha)=\sum_{m\le y}\Lambda(m)e(m\alpha)$、$P_g(\alpha)=\sum_m\Lambda(m)g(m)e(m\alpha)$。若 $C^\sharp_y=\widehat{\mathbf1_{\mathfrak m}P_yP_g}$，则对带重 $W$ 的偶数窗口范数 $\|\cdot\|_{6,W}$ 有
$$
                     \|C^\sharp_y-C\|_{6,W}\ll B_X^{1/6}.       \tag{2}
$$
这里依次使用宽 $X^{4/5}$ 的平滑、分母一显式公式移出极点、小弧内 $X|\alpha|\le T$ 的六阶界。三项均已独立建立。[1,2,3] 下文零点先截在 $|\gamma|\le X^2$；光滑性使任意受限子和的尾均为 $O_A(X^{-A})$。[1]



## 两次 Mellin 采样控制单个位置

<small>原稿第 3 页</small>

用长度 $\lambda=L/\lceil12L\rceil$ 的小格 $J_b=[b\lambda,(b+1)\lambda)$ 细分高度轴，$1/13\le\lambda\le1/12$。小格精确细分前稿的宽 $L$ 段。令 $Y=\max(1,y)$，定义非负数组
$$
  P_{bc}(n)=\sum_{\gamma\in J_b,\ \tau\in J_c}|A_{\gamma\tau}(n)|.
$$
以下界对固定的每一个 $n$ 成立，并保留一个位置内部 Fourier 积分的振荡：
$$
                    \sum_{b,c}P_{bc}(n)^2\ll Y L^4.              \tag{3}
$$
证明。Riemann–von Mangoldt 公式给出每一单位高度区间含 $O(L)$ 个零点，计重。[4] 若 $H(\xi)=\int h(u)e^{i\xi u}du$，$h$ 支撑于长 $O(1)$ 的区间，则 $\sum_\gamma m_\gamma |H(\gamma)|^2\ll L\|h\|_2^2$。可先平移支撑到原点附近，在每个单位区间用 $\sup |H|^2\le\int |H|^2+2\int |HH'|$，再在全轴用 Plancherel。两个坐标依次施行给 $O(L^2)$。

写 $V_0(v)=\int_E e(-\alpha v)d\alpha$。将第一条腿分在 $S\le t<4S$，其中 $S=1,4,16,\ldots$。对该块，无重数系数是
$$
 \iint f(t)g(s)t^{-1/2+i\gamma}s^{-1/2+i\tau}V_0(n-t-s)\,dt\,ds .
$$
在 $\log t,\log s$ 两个坐标里支撑长度均为 $O(1)$。经换元，输入的平方积分等于 $\iint |f(t)g(s)V_0(n-t-s)|^2dt\,ds\ll S$，因为 $\|V_0\|_2^2=|E|\le1$。在每个小格对上按正权 $m_\gamma m_\tau$ 作 Cauchy–Schwarz，花费的总重数至多 $O(L^2)$。再用两次采样，块的数组平方和至多 $CSL^4$。对这些数组的 $\ell^2$ 范数求和，$\sum_{S\le Y}\sqrt S\ll\sqrt Y$，即得 (3)。它还允许在各小格内部继续加上任意筛选条件。



## 三对三的 Cauchy–Schwarz

<small>原稿第 4 页</small>

将正侧的六个小格编号组成 $\mathbf i=(i_1,\ldots,i_6)$，令
$$
 U_n(\mathbf i)=P_{i_1i_2}(n)P_{i_3i_4}(n)P_{i_5i_6}(n).
$$
负侧用同一个数组；取共轭保持模长。式 (3) 给出 $\sum_{\mathbf i}U_n(\mathbf i)^2\ll Y^3L^{12}$。设一个受限区域的格对由 $0,1$ 矩阵 $K$ 覆盖，最大行和、列和均不超过 $\Delta$。给原分离条件取交只会减少绝对和。因为 $2uv\le u^2+v^2$，
$$
 \sum_{\mathbf i,\mathbf j}K_{\mathbf i\mathbf j}
       U_n(\mathbf i)U_n(\mathbf j)
       \le \Delta\sum_{\mathbf i}U_n(\mathbf i)^2 .
$$
窗口内有 $O(X)$ 个偶数，故这部分的逐项模长总和满足
$$
           \mathcal A(K;y)\ll \Delta X Y^3 L^{12}.                 \tag{4}
$$
因此在最长前缀上可容许 $\Delta\ll X^{3/2}$。此处的绝对值取在每个 $A_{\gamma\tau}(n)$ 已经形成之后。

固定正负两侧高度之间的一个配对。要求前五个高度差各落在长度 $R_j$ 的给定区间内，总差落在 $[\omega-A,\omega+A]$。固定一侧全部小格，另一侧的前五个小格各有 $O(1+R_j)$ 个选择。确定这五个后，总差使其第六个小格只有 $O(1+A)$ 个选择，因小格宽度在两个绝对常数之间。反方向的计数相同。于是
$$
 \mathcal A\ll XY^3L^{12}(1+A)\prod_{j=1}^{5}(1+R_j).             \tag{5}
$$
取 $A=1$、$R_j=X^{3/10}$，五个窗口共给 $X^{3/2}$，恰好达标。固定多个配对可用有限并。若同时放开许多互不相同的窗口中心，须对它们的并重新计算行、列和。式 (5) 对每组指定窗口一致。



## 总高度接近时一行能有多大

<small>原稿第 5 页</small>

取 $B=X^{9/10}$。在 $[B,2B]$ 选六个长度 $\asymp B$、相互间隔 $\gg B$ 的子区间。每区间有 $\gg B\log B$ 个零点，任一小格只有 $O(L)$ 个，故每区间至少有 $\gg B$ 个含真实零点的小格。[4] 六个坐标各取自己区间里的一个小格，共得 $\gg B^6$ 组。它们的编号总和只取 $O(B)$ 个整数值。某一固定总和的格组族 $\mathcal V$ 因而满足 $|\mathcal V|\gg B^5$。

固定 $\mathbf i\in\mathcal V$。在 $\mathcal V$ 中要找 $\mathbf j$，若其某一坐标离对应的 $i_k$ 在高度上不超过 $3L$，这个坐标有 $O(L)$ 个可能。另选四个坐标，最后一个由总和确定。因此须剔除的格组数为 $O(LB^4)$。不同区间本已间隔 $\gg B$。其余 $\gg B^5$ 个选择里，十二枚高度可以全部相距超过 $L$ 并满足原段号限制；这里剔除用了 $3L$ 的余量。且两组六个小格的总编号相同，实际总高度差小于 $6\lambda\le1/2$。

所以仅按 $|\sum\delta_j|\le1$ 与段号分离构造的格关系，在 $\mathcal V$ 上每行至少有 $cB^5$ 个允许项。该对称 $0,1$ 矩阵在 $\mathcal V$ 的常数向量上的 Rayleigh 商也至少为 $cB^5$，而 (4) 在 $y\asymp X$ 的预算是 $X^{3/2}$。这是对无权格关系的下界。实际六阶矩中的向量由带符号 Fourier 积分给定，以上计数没有给它的二次型下界。

经典加法大筛对分离的取样点给均方估计。[5] 在此处若将每组六个高度的总和当作新的取样点，原先对单枚高度的分离不能保证这些新点分离。第 4 页的五个附加区间正是用来使行、列和满足预算。



## 允许把原高度网格推到四分之一次幂

<small>原稿第 6 页</small>

令 $h\ge1$，用宽 $h$ 的段重新执行原来的跨位置分离，记局部带符号和为 $d_h(n)$，$D_h(y)=\sum_n' W(n/X)d_h(n)$。交换正负两侧可知 $d_h(n)$ 为实数。单点的比较为
$$
 |d_h(n)-|C(n)|^6|
    \ll\sum_{s=2}^6 U_h^s |C(n)|^{6-s},\qquad U_h=\sqrt X\,hL^2 . \tag{6}
$$
这里和下文省略任意负幂的截断尾。

若一个位置的两枚段号都受约束，第 3 页证明把每格重数上界改为 $O(hL)$ 即给数组范数 $\ll\sqrt X\,hL^2$。若只约束一枚，先将自由的另一条腿按符号求成 $Z_w$。对固定 $n$，其逆 Fourier 变换在实轴上的 $L^2$ 范数至多 $O(\sqrt{XL})$。受约束的腿在对数轴支撑长至多 $O(L)$，上述一次采样多出 $1+O(L)$，段内再用 Cauchy–Schwarz。因此单段数组范数 $\ll\sqrt{Xh}\,L^2\le U_h$。

对不同位置两条腿的段号差为 $-1,0,1$ 的诸等式作有限容斥。每个相容的交集将被牵涉的段号写为若干独立整数加固定偏移。每个独立整数至少在两个不同位置出现。固定其余整数，在两处用 Cauchy–Schwarz，在其他出现处用 $\ell^\infty\le\ell^2$；消去该整数后继续。同一位置两条腿若共用这个整数，改取无重复的斜对角。触及 $s$ 个位置就花费 $O(U_h^s)$，未触及的位置仍按原符号合成 $C(n)$ 或其共轭。这证明 (6)。

对 (6) 带窗求和并用 Hölder。令 $V=XU_h^6$，则
$$
              |D_h-M|\ll\sum_{s=2}^6 V^{s/6}M^{1-s/6}.             \tag{7}
$$
取 $h=L\lfloor X^{1/4}/L\rfloor$，使粗网格边界与旧网格对齐。此时 $V\ll B_X$。若 $M$ 大于充分大常数倍的 $B_X$，右端至多为 $M/2$。结合 (1) 得
$$
       \sup_y D_{\rm sep}(y)\ll B_X\quad\Longleftrightarrow\quad
       \sup_y D_h(y)\ll B_X .                                      \tag{8}
$$
这是单侧等价归约。式 (7) 中的 $M$ 仍是未知量。



## 哪些输出承载尚待估计的和

<small>原稿第 7 页</small>

回到真正定义 $D_{\rm sep}$ 的 $h=L$，于是 $U=\sqrt X\,L^3$。当 $|C(n)|\ge U$ 时，式 (6) 的误差至多 $O(U^2|C(n)|^4)$。因此 $|C(n)|$ 大于充分大常数倍的 $U$ 时，$d_L(n)\ge |C(n)|^6/2$。其余 $n$ 上有 $|d_L(n)|=O(U^6)$。写 $r_-=\max(0,-r)$，得到
$$
        \sum_n'W(n/X)(d_L(n))_-\ll XU^6=X^4L^{18}.                \tag{9}
$$
这个界控制所有输出逐点负部的总和，比从 $M\ge0$ 与 (1) 得到的整体下界更精细。

令 $T_0=X^{3/4}L^2$，记 $M_>(y)=\sum_{|C(n)|>T_0}'W(n/X)|C(n)|^6$。对 $|C|\le T_0$，每个输出贡献 $O(T_0^6)$，整个窗口共 $O(B_X)$。对 $|C|>T_0$，误差与主项之比为 $O((U/T_0)^2)$。所以
$$
 |D_{\rm sep}(y)-M_>(y)|
     \ll B_X+X^{-1/2}L^2 M_>(y).                                  \tag{10}
$$
这说明，在原分段表示中，跨不同整数 $n$ 的正负抵消能够承担的范围已经受限。对大输出，还需利用形成同一个 $C(n)$ 的两条素数腿。

下两页转回真实的素数对。对较短的锐截点区间，算术大筛直接给出 $M_>(y)$ 所需的规模，也能将其结论传回整个 $D_{\rm sep}(y)$。


## 直接对素数对作加法大筛

<small>原稿第 8 页</small>

令 $I\subset[1,2X]$ 为长至多 $Y$ 的区间，$X^{4/5}\le Y\le2X$，$n$ 是窗口内的偶数。置 $z=\sqrt Y$。要使 $m,n-m$ 均为大于 $z$ 的素数，$m$ 在每个 $p\le z$ 上须避开 $0,n\bmod p$。记禁类集为 $\mathcal F_p$，其大小 $\nu_p$ 为 $p\mid n$ 时的一，否则为二。偶数 $n$ 保证 $\nu_p<p$。令 $\mathcal S$ 是 $I$ 中避开所有禁类的整数，$S(a/q)=\sum_{m\in\mathcal S}e(am/q)$。加法大筛给 [5]
$$
 |\mathcal S|\le\frac{Y+O(1)+z^2}{G(z)},\qquad
 G(z)=\sum_{q\le z}\mu(q)^2\prod_{p\mid q}\frac{\nu_p}{p-\nu_p}. \tag{11}
$$
确实，取局部函数 $c_p(r)=1-(p/\nu_p)\mathbf1_{\mathcal F_p}(r)$。均值为零，均方为 $(p-\nu_p)/\nu_p$，在 $\mathcal S$ 上恒为一。对无平方因子 $q$ 作乘积 $c_q$，由中国剩余定理，其 Fourier 展开只含 $(a,q)=1$ 的频率。对 $\sum_{m\in\mathcal S}c_q(m)$ 的 Fourier 系数用 Cauchy–Schwarz 和 Parseval，得
$$
 |\mathcal S|^2\prod_{p\mid q}\frac{\nu_p}{p-\nu_p}
                    \le\sum_{a\bmod q}^{*}|S(a/q)|^2 .
$$
对 $q\le z$ 求和，既约分数的圆周间距至少 $z^{-2}$，即得 (11)。

设 $w=z^c$，其中 $c>0$ 是充分小的绝对常数。将 $p\le w$ 的完整乘积 $\prod(1+\nu_p/(p-\nu_p))$ 归一化为无平方因子 $d$ 上的概率。则 $\mathbb E\log d=\sum_{p\le w}\nu_p(\log p)/p\ll\log w\le\frac12\log z$，最后一步通过选择 $c$ 保证。因此至少一半权重在 $d\le z$。令 $S_n$ 为二元 Goldbach 奇异级数。在偶数 $n$ 上其可变因子是 $\prod_{p\mid n,p>2}(p-1)/(p-2)$。将完整乘积逐素数与 $\prod_{p\le w}(1-1/p)^{-2}$ 比较，得到
$$
        G(z)\gg (\log w)^2/S_n,\qquad S_n\ll \ell .
$$
后式用 $S_n\ll n/\varphi(n)$，对 $p\le\log(3n)$ 用 Mertens 乘积估计，较大素因子的倒数和为 $O(1)$。[6] 因 $\log z\asymp L$，式 (11) 给素数对数目 $\ll YS_n/L^2$，两素数均大于 $z$。



## 完整分离和的截点范围

<small>原稿第 9 页</small>

对上一页的 $I=(y_0,y_1]$，整圆系数 $R_I(n)=\sum_{m\in I}\Lambda(m)\Lambda(n-m)g(n-m)$ 非负。大素数对乘回各自对数后，由 (11) 贡献 $O(YS_n)$。任一素数至多 $z$，或任一数为高次素数幂的项，总权 $\ll (z+\sqrt X L)L^2\ll Y$。后者只需计数 $O(X)$ 内的高次素数幂。故 $R_I(n)\ll Y\ell$。奇异级数主项 $S_n\int_I\eta((n-t)/X)dt$ 亦为 $O(Y\ell)$。

令 $c_I=C^\sharp_{y_1}-C^\sharp_{y_0}$。取两端点的主弧误差之差 $e_I(n)$，前稿式 (6) 给 $\|e_I\|_{6,W}^6\ll_\varepsilon X^{26/5+\varepsilon}$。[2,3] 整圆减主弧给 $|c_I(n)|\ll Y\ell+|e_I(n)|$。GRH 下 $\sum_{m\in I}\Lambda(m)\ll Y+\sqrt X L^2\ll Y$；对原始素数多项式用 Parseval 以及 $\sup_{\mathfrak m}|P_g|\ll X^{3/4}L^{3/2}$，得
$$
              \sum_n|c_I(n)|^2\ll X^{3/2}Y L^4 .
$$
在 $|c_I(n)|\le C Y\ell$ 用四次上确界乘这项均方；取 $C$ 足够大后，其余处 $|c_I(n)|\ll|e_I(n)|$。由此
$$
 \|c_I\|_{6,W}^6\ll_\varepsilon
            X^{3/2}Y^5 L^4\ell^4+X^{26/5+\varepsilon}.             \tag{12}
$$
$Y=Y_*$ 时第一项恰为 $B_X$；取固定 $\varepsilon<3/10$，第二项更小。较短区间同样可按 $Y=Y_*$ 估计。因此由 (1)、(2) 及窗口范数的三角不等式，
$$
 |D_{\rm sep}(y)|\ll B_X+X^{3/2}y^5L^4\ell^4
                  \quad(0\le y\le2X).                             \tag{13}
$$
特别是 $0\le y\le Y_*$ 的**完整**分离和达标。取 $\mathcal G=\{jY_*:0\le jY_*\le2X\}\cup\{2X\}$。若只知网格点上的单侧上界，则 (1) 先给网格点上 $M\ll B_X$，(2) 移到锐前缀，(12) 控制到左网格点的单次增量，再由 (2)、(1) 返回 $D_{\rm sep}$。这给出
$$
 \sup_{0\le y\le2X}D_{\rm sep}(y)\ll B_X
      \quad\Longleftrightarrow\quad
 \max_{z\in\mathcal G}D_{\rm sep}(z)\ll B_X .                       \tag{14}
$$
较小间隔通过一次比较处理，误差不会沿网格逐次累加。网格点数为 $O(1+X^{1/5}\ell^{4/5}/L^{8/5})$。



## 先对整条前缀腿用 Cauchy–Schwarz 会损失多少

<small>原稿第 10 页</small>

令 $G=\mathbf1_E Z_g$，$v_n=\mathbf1_{2\mid n}W(n/X)^{1/6}$。从 $L^2(\mathbb T)$ 到窗口 $\ell^6$ 的算子取为 $TF(n)=v_n\widehat{FG}(n)$。它的对偶形式是
$$
 \|T^*x\|_2^2=\sum_{n,m}v_nv_m\overline{x_n}x_m K(n-m),\quad
 K(h)=\widehat{|G|^2}(h).
$$
若把 $F=Z_f$ 只通过 $\|F\|_2\ll\sqrt{XL}$ 输入，Cauchy–Schwarz 加 $\ell^6$ 对偶需要一条均匀的 Gram 上界
$$
             \sup_{\|x\|_{6/5}=1}\|T^*x\|_2^2
                      \ll B_X^{1/3}/(XL)=X^{5/6}L^3.               \tag{15}
$$
取 $x$ 为 $[X,2X]$ 中一个偶数处的单位点质量，左端至少为 $K(0)$。这里可以计算真实第二条腿本身的大小。前稿已证
$$
 \int_{\mathfrak m}|P_g|^2
       =(7/10+o(1))X\log X\int \eta(u)^2du .                       \tag{16}
$$
在小弧上 $Z_g-P_g=O(L)$，因为主极点在该区域快速衰减。[2,3] 近原点部分满足 $\int_{\mathfrak m\setminus E}|Z_g|^2\ll TL^2=o(XL)$。[1] 从 (16) 得 $K(0)\asymp XL$，超过 (15) 的量级。事实上，取 $F=\sqrt{XL}\,\overline G e(n_0\alpha)/\|G\|_2$，单个 $n_0$ 的六阶贡献就有 $\asymp X^6L^6$。$F$ 是用来测试算子范数的函数。对实际 $Z_f$，(9)、(10) 已说明，所需的抵消必须在这些大输出形成时发生。

**仍待证明的量。** 在 (14) 的长前缀网格点上，(5) 处理一整类局部高度差配置，(8) 允许把全部跨位置的段分离推至 $X^{1/4}$ 尺度。对其余配置，还缺在同一 $n$、同一截点上把真实两条腿的相位联系起来的上界。式 (13) 对 $y\asymp X$ 给 $O(X^{13/2}L^4\ell^4)$；所需的 $X$ 幂次节省仍然存在。



## 三个长截点足以检测缺少平衡素数对的偶数

<small>原稿第 11 页</small>

附件以 $I=(1/3,2/3)$ 压缩 $T_N$，并在式 (2a) 给出累计偏差与 $\|B_N\|$ 的比较。[7] 先只问 $N\in[X,2X]$ 能否表示为两枚都在 $NI$ 中的素数。取
$$
       \mathcal Y_X=\{X/2,\,2X/3,\,5X/6\},\qquad
       M_3^+=\max_{y\in\mathcal Y_X}(D_{\rm sep}(y))_+ .
$$
当 $X\le N\le3X/2$ 时，取头两个截点之间的 $J=(X/2,2X/3]$；当 $3X/2<N\le2X$ 时，取后两个之间的 $J=(2X/3,5X/6]$。两段长度同为 $X/6$。除至多一个端点，$J$ 内的 $m$ 和 $N-m$ 都严格落在 $NI$ 内。整个积分段上 $\eta((N-t)/X)=1$。

写 $J=(u,v]$，$E_y(N)=\widehat{\mathbf1_{\mathfrak M}P_yP_g}(N)-S_N\int_0^y\eta((N-t)/X)dt$ 为主弧误差。圆法的精确差分给
$$
 R_J(N)-S_N X/6
 =C^\sharp_v(N)-C^\sharp_u(N)+E_v(N)-E_u(N).
$$
由前稿主弧六阶界，$\sup_{y,N}|E_y(N)|\ll_\varepsilon X^{13/15+\varepsilon}$，此处 $W(N/X)=1$。[2] 由 (1)、(2)，三个截点上分别有 $|C^\sharp_y(N)|\ll (B_X+M_3^+)^{1/6}$。高次素数幂和端点的总权 $O(\sqrt X L^3)$。所以
$$
 M_3^+=o(X^6)\quad\Longrightarrow\quad
 \#\{p+q=N:\ p,q\ {\rm prime},\ p,q\in NI\}
                   \gg XS_N/L^2                                  \tag{17}
$$
对全部窗口内偶数一致，这里按有序对计数。确实，$B_X=o(X^6)$ 且 $S_N\gg1$，因此 $R_J(N)=XS_N/6+o(X)$，每个素数对权重至多 $O(L^2)$。

若 $\mathcal E_X$ 为没有平衡素数对的偶数集，同一差分给每个 $N\in\mathcal E_X$ 至少一个截点上 $|C^\sharp_y(N)|\gg XS_N$。分别用这三个截点的二阶和与六阶和，得到
$$
 \sum_{N\in\mathcal E_X}S_N^2\ll X^{1/2}L^4,\qquad
 \sum_{N\in\mathcal E_X}S_N^6\ll X^{-6}(B_X+M_3^+).              \tag{18}
$$
第一式用 $\sum_n|C^\sharp_y(n)|^2\ll X^{5/2}L^4$。第二式以 (1)、(2) 求和。式 (17) 只给充分条件；当前三点上的 $o(X^6)$ 仍待证明。



## 压缩算子的首奇异值需要多少截点

<small>原稿第 12 页</small>

仍在 $N\in[X,2X]$。取整数 $8\le K\le X^{1/5}$，全窗口共用截点 $y_j=jX/K$，$0\le j\le2K$，置 $M_K^+=\max_j(D_{\rm sep}(y_j))_+$。对附件中的真实平衡压缩有
$$
 \max_{N\in[X,2X],\,2\mid N}\frac{\|B_N\|}{S_N}
       \ll \frac1K+\frac{(B_X+M_K^+)^{1/6}}{X}.                    \tag{19}
$$
证明。用附件的 $\nu_N$，记 $P_N(x)=S_N(x-1/3)-\nu_N((1/3,x])$。任一长度至多 $X/K$ 的物理区间，真算术测度的质量上界由 (11) 得
$$
 \nu_N(J/N)\ll S_N\,\frac{X}{NK}+N^{-1/2}L^3\ll S_N/K .
$$
此处必须保留筛界里的 $S_N$。小素数及高次幂的处理同第 9 页；$X/K\ge X^{4/5}$。于是 $P_N$ 在任一网格单元中波动至多 $O(S_N/K)$。每个 $NI$ 内都有网格点，且每个 $NI$ 中的点离一个同区间网格点至多一个步长。

在 $NI$ 内固定任一网格点作锚点。它与另一网格点之间的 $P_N$ 差，由第 11 页的精确差分除以 $N$ 给出，符号取负。恢复 $(m,N)=1$ 的修正为 $O(L^3/N)$，因为非互素且 $\Lambda(m)\ne0$ 时 $m=p^k$、$p\mid N$。所需的两端主弧误差已受 $B_X^{1/6}$ 控制。由 (1)、(2)，相邻单元的波动与网格点相对锚点的偏差合计至多 $O(S_N/K+(B_X+M_K^+)^{1/6}/N)$。代入附件式 (2a) 的右侧即得 (19)。

这也给出固定 $c>0$ 下的实际例外集界。先取仅依赖 $c$ 的常数 $K$ 使单元波动小于 $cS_N$ 的适当固定分数。保留上述证明中各自 $N$ 处的真实 $C^\sharp_{y_j}(N)$，则 $\|B_N\|\ge cS_N$ 迫使某一网格点满足 $|C^\sharp_{y_j}(N)|\gg_c XS_N$。对 $O_c(1)$ 个截点使用二阶和，得
$$
 \sum_{\substack{X\le N\le2X,\ 2\mid N\\\|B_N\|\ge cS_N}} S_N^2
                           \ll_c X^{1/2}L^4.                       \tag{20}
$$
要排除所有这类缺陷，(19) 仅需 $K\to\infty$ 且 $M_K^+=o(X^6)$，例如可取 $K=\lceil\log\log X\rceil$（对充分大 $X$）。这给的是 $B_N$。附件中的全空间 $T_N$ 还包含平衡测试空间以外的方向。[7,8]



## 依据与 Lean 核验范围

<small>原稿第 13 页</small>

[1] [《哥德巴赫六阶矩中的不相交零点》](11-zeros.md)，式 (3)–(11) 给出 $D_{\rm sep}$ 的原定义、局部采样与完整矩的比较。当前的 $D_h$ 也只用于零点高度。另稿有限域中的反射中心有不同的定义。

[2] [《哥德巴赫六阶矩的主弧与共振小弧》](07-arcs.md)，式 (6)、(12) 与第 10 页的光滑素数和真实小弧质量。其主弧误差估计只使用窗口内 $n\asymp X$ 及 $O(X)$ 个整数。

[3] [《哥德巴赫六阶矩的 Mellin 分解》](08-mellin.md)，短区间截点估计 (10)；[《哥德巴赫六阶矩的五模数项》](10-moduli.md)，第 11–12 页的分母一显式公式与极点转移。

[4] K. Chandrasekharan，[Lectures on the Riemann Zeta-Function](https://mathweb.tifr.res.in/Documents/Publications/Lectures/tifr01.pdf)，第 9 节，Riemann–von Mangoldt 零点计数主公式与单位区间推论。

[5] H. L. Montgomery、R. C. Vaughan，[The large sieve](https://doi.org/10.1112/S0025579300004708)，Mathematika 20 (1973)，定理 1。式 (11) 给出在当前二元素数筛中的具体应用。

[6] V. Shoup，[A Computational Introduction to Number Theory and Algebra](https://www.ece.uvic.ca/~fayez/research/gf3m/shoup_b08.pdf)，第 5.3 节，Mertens 估计。用 Chebyshev 上界与分部求和即可得 $\sum_{p\le w}(\log p)/p\ll\log w$。

[7] [附件《哥德巴赫算子的三个范数估计》](02-operator.md)，第 1–2 页，压缩的混合矩阵元、奇异值界及累计偏差比较 (2a)。

[8] 李嘉旻、刘建亚，[A Conditional Proof of the Goldbach Conjecture](https://mrc.sdu.edu.cn/english/info/1018/1514.htm)，两种谱假设及平衡素数对结论。

**Lean 4 的范围。** 配套文件在 Lean 与 mathlib 4.19.0 中检查带重分格的 Cauchy–Schwarz、不对称关系的行列界、三次张量平方和、六维总和编码的单射与基数上界、误差吸收、大输出正性、局部筛权均值和均方、筛分母截断、六次幂截断、平衡检测区间及端点证据的加权计数等有限步骤。零点采样、连续 Fourier 分析、GRH 输入和整段截点估计由正文的数学推导给出。全区间目标保持待证。
