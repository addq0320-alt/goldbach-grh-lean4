# 哥德巴赫六阶矩的反射、几何与正迹

<small>原稿第 1 页</small>

设 $L=\log(2X)$，$B_X=X^{11/2}L^{12}$。在前稿的 GRH 与等宽圆法设置下，以下三个结论分别作用于真实小弧卷积、四模数 Kloosterman 子问题及真实系数的有限 Fourier 变换。

**反射中心。** 可以对所有锐截点 $0\le y\le2X$ 同时选一组有限域特征，使每个输出 $n$ 精确展开为反射对 $(c,n-c)$ 的和及一个可控 Fourier 模式。令
$$
                         H=\lfloor\sqrt X\,L^2\rfloor .
$$
只保留六个反射对的十二个中心彼此循环距离都大于 $H$ 的带符号子和，记为 $D_H(y)$。则
$$
 \sup_y\operatorname{Re}\mathcal J_y\ll B_X
           \quad\Longleftrightarrow\quad \sup_y D_H(y)\ll B_X.         \tag{1}
$$
这里中心属于辅助素域。证明使用混合特征四阶矩、前缀最大不等式和有界度图的求和。大半径结论通过吸收含未知矩的项得到。

**四模数。** 对四个互异奇素模数 $p_i\asymp\sqrt X$，局部参数均可逆，沿共同变量 $n$ 的四个归一化 Kloosterman 和之积，在长度 $X$ 的固定光滑窗口中的和为 $O(X^{7/8})$。锐区间的界为 $O(X^{7/8}L^{1/2})$。这改进了上一稿对临界模数积的 $O(X)$ 估计。

**正迹。** 对真实窗口系数作二次和三次 Fourier 相位扭转。两个参数均匀平均后的六阶矩有精确公式，并满足 $O(B_X)$。还能在原六阶矩中，以绝对值总和 $O(B_X)$ 移出同方差、同判别式的两组三元频率，其中包括关于共同重心互为反射的六个互异频率。

三个结论都保留原目标的对数次数。式 (1) 右端以及正迹在指定零扭转处的上界仍待证明。



## 把原小弧精确移到有限群

<small>原稿第 2 页</small>

令 $F_y(m)=\Lambda(m)\mathbf1_{1\le m\le y}$，$G(m)=\Lambda(m)\eta(m/X)$。前稿固定 $\eta$ 的支撑在 $(1/8,2)$，$W$ 支撑在 $(0,3)$、在 $[1,2]$ 为一、$0\le W\le1$。$\mathfrak m$ 为从单位圆删去所有 $q\le X^{3/10}$、半宽 $L^4/X$ 的主弧所得。写 $e(z)=\exp(2\pi iz)$，$P_F(\alpha)=\sum_m F(m)e(m\alpha)$。实际研究的是
$$
 C_y(n)=\widehat{\mathbf1_{\mathfrak m}P_{F_y}P_G}(n),\qquad
 M(y)=\sum_{n\in2\mathbb Z}W(n/X)|C_y(n)|^6 .
$$
这里 Fourier 系数用负号。前稿证明 $M(y)-\operatorname{Re}\mathcal J_y=O(B_X)$，且 $\|C_y\|_\infty\ll XL$、$\sum_n|C_y(n)|^2\ll X^{5/2}L^4$，均对 $y$ 一致。[1]

由 Bertrand 定理取 $32X<p<66X$ 的素数。所有有限域卷积均用计数测度，$\ell^2$ 范数也不归一化。取固定 $\phi\in C_c^\infty((-1/2,1/2))$，在 $[-1/5,1/5]$ 为一。对 $k\in\mathbb F_p$ 用中心代表元 $\widetilde k$ 定义
$$
 d(k)=\phi(\widetilde k/p)\,\widehat{\mathbf1_{\mathfrak m}}(\widetilde k),
                  \qquad G'=d*G .
$$
时间变量 $m,r$ 及窗口内 $n$ 满足 $|n-m-r|\le 4X<p/5$。故直接展开积分即得 $C_y(n)=(F_y*G')(n)$，在窗口内对每个整数都精确相等。

若 $e_p(t)=e(t/p)$，$d$ 的未归一化 Fourier 乘子是 $\int_{\mathfrak m}\sum_k\phi(k/p)e(-k(\alpha+j/p))d\alpha$。Poisson 求和后，内核在圆上的 $L^1$ 范数至多为 $\|\widehat\phi\|_1$。所以
$$
 \|G'\|_2\ll\|G\|_2\ll\sqrt{XL},\qquad \|F_{2X}\|_2\ll\sqrt{XL}.     \tag{2}
$$
此处只需 $\sum_{m\le2X}\Lambda(m)^2\ll XL$。尖锐的小弧指示函数仍在 $d$ 中。



## 加法和乘法特征的反射展开

<small>原稿第 3 页</small>

对模 $p$ 的非平凡乘法特征 $\chi$ 取 $\chi(0)=0$，取 $t\in\mathbb F_p$。令 $K(x)=\chi(x)e_p(tx)$，$K'(x)=\bar\chi(x)e_p(tx)$。对函数 $F$ 写
$$
 \lambda_t(F)=p^{-1}\sum_x F(x)e_p(-tx),\qquad
 u_F(c)=p^{-1}\sum_x F(x)\overline{K(x-c)} .
$$
第二条腿的 $v_G(d)$ 以 $K'$ 代 $K$ 定义。非平凡乘法特征有完全相关
$$
 \sum_c\chi(x-c)\bar\chi(z-c)=p\mathbf1_{x=z}-1 .
$$
相等时逐项相加得 $p-1$。不等时，分式 $(x-c)/(z-c)$ 将 $c\ne z$ 双射至 $\mathbb F_p\setminus\{1\}$，非平凡特征总和为零。因此
$$
 F(x)=\lambda_t(F)e_p(tx)+\sum_c u_F(c)K(x-c),\qquad
 \sum_c u_F(c)e_p(-tc)=0 .
$$
另一条腿有同样的重构。两个平移基函数的卷积为
$$
 (K(\cdot-c)*K'(\cdot-d))(n)
 =\chi(-1)\{p\mathbf1_{n=c+d}-e_p(t(n-c-d))\}.
$$
因为 $(x-c)/(n-d-x)$ 在 $n\ne c+d$ 时取遍除 $-1$ 外的域元素。$\chi(-1)$ 总是 $\pm1$。基函数与单独的加法模式卷积为零，第二项在完整重构中也相消。写 $u_y=u_{F_y}$，$v=v_{G'}$，在窗口上得到
$$
 \begin{aligned}
 C_y(n)&=b_y(n)+\sum_c w_{y,n}(c),\\
 b_y(n)&=p\lambda_t(F_y)\lambda_t(G')e_p(tn),\\
 w_{y,n}(c)&=\chi(-1)p\,u_y(c)v(n-c).
 \end{aligned}                                                       \tag{3}
$$
一个 $c$ 已经决定了同一位置的另一个中心 $n-c$。



## 同一组特征适用于所有锐截点

<small>原稿第 4 页</small>

暂时对所有乘法特征与所有 $t$ 均匀平均，并将平凡特征在零点也置零。对固定中心 $c$、有限系数 $a_x$，正交性给
$$
 \mathbb E_{\chi,t}\left|\sum_x a_x\overline{K(x-c)}\right|^4
                         \le 2\left(\sum_x|a_x|^2\right)^2.          \tag{4}
$$
展开后，存活的四个变量满足 $x_1+x_2=x_3+x_4$ 及 $(x_1-c)(x_2-c)=(x_3-c)(x_4-c)\ne0$。其和及积都相等，故两对变量是同一重集。剔除平凡特征只使正平均界多一个 $(p-1)/(p-2)$ 因子。

式 (4) 在对有序前缀取最大值后仍成立，只需改变绝对常数。设能量 $E=\sum |a_x|^2$。按顺序取能量中位点，将区间拆成左子区间、中位点及右子区间，使每个子区间的能量至多为父区间的一半。递归时空区间或零能量区间终止。第 $j$ 层各父区间能量至多 $2^{-j}E$。同层出现的子区间及中位点两两不交，总能量至多 $E$。故由 (4)，该层所有块的和的模之最大值，其 $L^4(\chi,t)$ 范数至多 $C2^{-j/4}\sqrt E$。任一前缀在每层至多用一个完整子区间和一个中位点，沿切点继续递归。对最大值应用 Minkowski 并求几何级数即证。此类最大不等式也见 [2]。

对中心求和，代入 (2)，同时对 $G'$ 使用非最大版本。再用 $\mathbb E_t|\lambda_t(G')|^2=p^{-2}\|G'\|_2^2$。将三个非负量分别除以各自平均上界后相加，可以选到同一组 $(\chi,t)$ 使
$$
 \sum_c\sup_y|u_y(c)|^4+\sum_d|v(d)|^4\ll L^2/p,\qquad
                   |\lambda_t(G')|\ll\sqrt{L/p}.                     \tag{5}
$$
由 $|\lambda_t(F_y)|\ll\sqrt L$ 有 $|b_y(n)|\ll\sqrt p\,L$。关键是逐个输出的均方
$$
 \sum_c |w_{y,n}(c)|^2
 \le p^2\Big(\sum_c|u_y(c)|^4\sum_d|v(d)|^4\Big)^{1/2}\ll pL^2 .    \tag{6}
$$



## 十二个中心的平方根尺度分离

<small>原稿第 5 页</small>

写 $\|a\|_p$ 为域元素中心代表元的绝对值。先从每个位置删去自身靠近的情形 $\|2c-n\|_p\le H$。至多 $2H+1$ 个中心被删去。由 (6)，每个输出删去的系数模至多 $O(\sqrt{Hp}\,L)$。这一界同样控制 (3) 的 $b_y(n)$。以 $C_*(n)$ 表示删除后全体中心的和，$M_*=\sum W|C_*|^6$，窗口和一律限于偶数。置 $U=\sqrt{Hp}\,L$，则
$$
        |M(y)^{1/6}-M_*^{1/6}|\ll X^{1/6} U,\qquad XU^6\ll B_X.     \tag{7}
$$
对 $M_*$ 展开后的六个位置，若两位置的任一中心循环距离至多 $H$，就在这两个位置间连边。在固定 $n$ 时，每条边对应对称关系，且每行、每列至多 $4(2H+1)$ 个邻居。对不同位置间存在边的事件作容斥，最多只有 $15$ 条候选边。

对一个非空交集，设 $s$ 个位置被涉及。保留各分量的一棵生成树，放宽其余边，上界涉及位置的绝对和。从叶子往内，每次对至多 $O(H)$ 个邻居求和，花费 $O(\sqrt H)\|w_{y,n}\|_2$。最后一条边的矩阵，其行和、列和至多 $O(H)$，由 Schur 界花费 $O(H)\|w_{y,n}\|_2^2$。不同分量相乘，固定 $n$ 的交集模至多 $O(U^s)|C_*(n)|^{6-s}$，保留了未涉及位置的符号。于是
$$
 |M_*-D_H(y)|\ll\sum_{s=2}^{6}(XU^6)^{s/6}M_*^{\,1-s/6}.           \tag{8}
$$
这里 $s=6$ 时最后的幂取一，$D_H$ 是全体十二个中心两两相距大于 $H$ 的子和，交换两侧知其为实数。若 $M_*\gg B_X$，右端除以 $M_*$ 后为 $O((B_X/M_*)^{1/3})$。这允许吸收一半 $M_*$，故 $M_*\ll (D_H)_++B_X$。反过来 $M_*\ll B_X$ 立即给 $|D_H|\ll B_X$。由 (7) 得 (1)。



## 小半径有独立上界

<small>原稿第 6 页</small>

大半径式 (8) 中含 $M_*$。若只删除不同位置间的近邻，取较短距离 $1\le h\le L^4$，可以直接对这部分带符号和给出数量级。此处暂时保留同一位置内部靠近的两枚中心，并在 (3) 中只展开中心和 $C^0=C_y-b_y$。令 $D^{\rm cross}_h$ 只排除不同位置的近邻，则
$$
 \left|\sum W|C^0|^6-D_h^{\rm cross}\right|
                         \ll h X^{11/2}L^8\le B_X .                  \tag{9}
$$
为核对对数，对窗口有 $\sup |C^0|\ll XL$ 及 $\sum W|C^0|^2\ll X^{5/2}L^4$。这来自第 2 页和 $|b_y|\ll\sqrt pL$。涉及两个位置时，唯一边的成本为 $O(hpL^2)$。其余四位置的带窗和至多为 $(XL)^2 X^{5/2}L^4$。相乘恰得 (9)。涉及三至六个位置时，替换成 $(\sqrt{hp}L)^s$。余下的三次、二次、一次、零次窗口和分别由上确界乘二阶和、二阶和、Cauchy–Schwarz、窗口长度控制。总 $X$ 指数依次为 $5,9/2,17/4,4$；$h$ 带来的额外固定对数由幂次余量吸收。

**与普通 Gowers 范数的联系。** 前稿的平移 Legendre 模型在 $U^3,U^4$ 中很小，却在固定反射点产生大系数。[1,3] 式 (4) 实际利用了乘法和加法两种正交性。四个点同和、又同平移后的积，才迫使两对完全一致。由此可控制每个 $n$ 的 (6)。最终仍须处理许多相距超过 $H$ 的反射对在这个 $n$ 上的相位。

$H$ 衡量的是选择特征后的有限域平移中心。前稿中的 $|\gamma-\gamma'|$ 衡量 $\zeta$ 零点高度。[1] 两种表示都给原问题的判据；将一个表示的筛选条件直接施加给另一个表示，还需要额外恒等式。



## 固定的 Legendre 反射能否出现在素数中

<small>原稿第 7 页</small>

混合平均之外，还可直接检验上一稿的特定障碍。仍取第 2 页的 $p\asymp X$、$p>32X$。对每个非平凡乘法特征 $\chi$、每个 $c\ne0$、每个 $t\bmod p$ 和每个 $0<\theta<1/24$，真实前缀满足
$$
 \sup_{0\le y\le2X}
 \left|\frac1p\sum_{m\le y}\Lambda(m)\chi(m-c)e_p(tm)\right|
                      \ll_\theta X^{-\theta}L^2.                     \tag{9a}
$$
这里的模数、特征、中心和锐截点都允许变化。

证明用 Fouvry、Kowalski、Michel 关于素数上迹函数的定理 1.5。[7] 对任一 $r$，$\chi(x-c)e_p(rx)$ 的秩一层在非零有限点 $c$ 有非平凡驯分歧，导子绝对有界。例外形状 $\chi_0(x)e_p(ax)$ 在 $c$ 无分歧。因此对任一固定光滑壳权 $\psi$、$S\ge2$，
$$
 \left|\sum_{\ell\ {\rm prime}}\psi(\ell/S)\chi(\ell-c)e_p(r\ell)\right|
       \ll_{\theta,\psi} S(1+p/S)^{1/6}p^{-\theta}
$$
一致于 $r,c,\chi$。为保留可动截点，把 $\mathbf1_{1\le m\le y}\log m$ 在模 $p$ 上展开成加法 Fourier 级数。其总变差 $O(L)$，归一化 Fourier 系数的绝对和 $O(L^2)$，由离散分部求和与调和级数即得。每个新频率只平移 $r$，适用同一定理。

用固定光滑二进分割覆盖 $2\le m\le2X$，可取全部壳支撑在 $m<p$，故模 $p$ 截点不产生周期混叠。几何级数给 $\sum_{S\ll X}S(1+p/S)^{1/6}\ll X$。高次素数幂的总权为 $O(\sqrt X L^2)$。除以 $p$ 即得 (9a)。若直接取上一稿模型的 $X=p$，文献的锐截点版本及分部求和也给原中心处 $O_\varepsilon(p^{-1/48+\varepsilon})$ 的归一化界。[7]

所以真实素数前缀与一条给定平移二次特征之间已有幂次抵消。式 (1) 仍涉及一个输出上许多不同中心的联合相关。




## 四个素模数合并后还保留什么相位

<small>原稿第 8 页</small>

设 $p_1,\dots,p_4$ 为互异奇素数，$k_i h_i\ne0\bmod p_i$。取
$$
 K_i(n)=p_i^{-1/2}S(k_i,(n-j_i)h_i;p_i),\quad
 S(k,b;p)=\sum_{x\ne0} e_p(kx+b/x).
$$
$K_i$ 是实数，因为 $x\mapsto-x$ 给共轭和。在归一化 Fourier 约定 $\widehat K_i(r)=p_i^{-1}\sum_nK_i(n)e_{p_i}(-rn)$ 下，零频系数为零，其余系数为
$$
 \widehat K_i(r)=p_i^{-1/2}e_{p_i}(k_i h_i/r-j_i r).
$$
令 $M=\prod p_i$，$M_i=M/p_i$，用中国剩余定理定义 $J\equiv j_i$、$A\equiv M_i^2 k_i h_i\bmod p_i$。乘积 $K(n)=\prod_i K_i(n)$ 在模 $M$ 上的 Fourier 系数恰为
$$
 \widehat K(r)=M^{-1/2}\mathbf1_{(r,M)=1}e_M(A/r-Jr).               \tag{10}
$$
式中倒数只在单位处取。局部 Fourier 频率为 $r/M_i\bmod p_i$，故出现 $M_i^2$。有限 Fourier 反演给 $K(n)=M^{-1/2}S(n-J,A;M)$。

为突破短窗，须对一个平移差再变换。略去下标，令 $a=kh$。定义 $K_s(n)=K(n+s)\overline{K(n)}$，此处 $K$ 指一个素模数因子。卷积 Fourier 系数给
$$
 \widehat K_s(u)=\frac{e_p(-ju)}p
  \sum_{r\ne0,u} e_p\!\left(sr+a/r-a/(r-u)\right).                 \tag{11}
$$
$u=0$ 时，$s=0$ 的值为 $(p-1)/p$，$s\ne0$ 的值为 $-1/p$。$u\ne0$ 时有两个不相消的简单极点，故有理函数不可能为 $g^p-g+$ 常数。导子有绝对常数界，有理函数的 Weil 界给 $|\widehat K_s(u)|\ll p^{-1/2}$。[4] 这也覆盖 $s=0,u\ne0$。



## 在临界模数积处省出八分之一次幂

<small>原稿第 9 页</small>

设 $R=p_2p_3p_4\ge X$，$p_i\ll\sqrt X$，$w$ 为固定光滑紧支撑函数。$S_w=\sum_n w(n/X)\prod_i K_i(n)$ 满足
$$
              |S_w|^2\ll_w Xp_1+X\sqrt R .                          \tag{12}
$$
按 $n\bmod p_1$ 分组，$\sum_{n\bmod p_1}|K_1(n)|^2=p_1-1$。Cauchy–Schwarz 后，第二个因子是其余三因子带权和在各同余类上的平方和。对角 $s=0$ 成本 $O_w(X)$，用到单素模数 Weil 界 $|K_i|\le2$。其余平移形如 $s=hp_1$，$0<|h|\ll_w X/p_1$。

写 $F_s(n)=\prod_{i=2}^4 K_i(n+s)\overline{K_i(n)}$。由 (11) 与中国剩余定理，
$$
 |\widehat F_s(u)|\ll R^{-1/2}\gcd(s,u,R)^{1/2}.
$$
平移后的权 $w_s(t)=w(t+s/X)\overline{w(t)}$ 导数有一致界。Poisson 求和与 $X\le R$ 给该平移和的模至多 $C_w\sqrt R\,\gcd(s,R)^{1/2}$，因为 $\sum_{\ell\in\mathbb Z}X|\widehat w_s(X\ell/R)|\ll_w R$。若为锐窗口，两个区间的交仍是区间，几何级数完成和额外花费 $\log(2R)$。

最后对 $h$ 平均，$(p_1,R)=1$ 且
$$
 \sum_{1\le h\le H_0}(h,R)^{1/2}
 \le H_0\sum_{d\mid R}d^{-1/2}\le 8H_0.
$$
乘回 $p_1$ 得 (12)。因此四个 $p_i\asymp\sqrt X$ 时为 $O_w(X^{7/8})$；若 $p_i\asymp\sqrt X/L$，光滑窗进一步给 $O_w(X^{7/8}L^{-3/4})$。限偶数用 $n=2m$ 即可。锐区间的相应通式在 (12) 的第二项乘 $\log(2R)$。这是算术 van der Corput 方法在本核上的一次差分。[5]

原 Type I 块确实含有这种单个 Kloosterman 和。[1] 将 (12) 用在完整六阶矩，还须证明四个因子共同依赖同一 $n$、外权具有规定的光滑性或有界变差，并处理非互素模数、非单位参数及其余系数。



## 对真实输出作三次 Fourier 扭转

<small>原稿第 10 页</small>

现在直接取 $a_n=\mathbf1_{2\mid n}W(n/X)^{1/6}C_y(n)$。按第 2 页的辅助素数将这段有限序列零延拓到 $\mathbb F_p$。令 $b_r=p^{-1}\sum_x a_x e_p(-rx)$，$Z_j=\sum_r|b_r|^{2j}$。Parseval 给 $Z_1\ll X^{3/2}L^4$。对 $u,v\in\mathbb F_p$ 定义
$$
 F(u,v)=\sum_{x\in\mathbb F_p}
    \left|\sum_r b_r e_p(xr+ur^2+vr^3)\right|^6 .
$$
$F(0,0)=M(y)$，而两参数平均有精确公式
$$
 \mathbb E_{u,v}F(u,v)=p(6Z_1^3-9Z_1Z_2+4Z_3)
                       \le 6p Z_1^3\ll B_X.                          \tag{13}
$$
展开并求和，正负两组三元组的前三个幂和都相同。因 $p>3$，Newton 恒等式恢复三个基本对称多项式，故两组三元组为同一重集。三枚不同、恰有两枚相同、三枚全同三种情形，对每个重集分别有 $36,9,1$ 种有序对。展开 (13) 右侧即得这三个系数。Markov 不等式随即将超过平均界 $K$ 倍的参数比例压至 $O(1/K)$。

指定参数 $(0,0)$ 可能与其余全部参数不同。取检验序列 $a_x=T\mathbf1_{x=x_0}$。原点的值为 $|T|^6$。每个非零 $(u,v)$ 的内和是二次或三次多项式的完全加法和乘以 $T/p$，故模长至多 $2|T|/\sqrt p$，从而
$$
 F(u,v)\le64|T|^6/p^2\quad((u,v)\ne(0,0)).
$$
取 $T=X$ 时这两个数量级分别是 $X^6$ 与 $O(X^4)$。这个检验说明，即使所有非零扭转都受控，仍需要用于真实系数 $a_n$ 的定点估计。[4]



## 移出重心反射的两组三元频率

<small>原稿第 11 页</small>

固定共同的一次和 $s$。对三元组 $r_1,r_2,r_3$ 置 $z_i=r_i-s/3$，并记 $Q=\sum z_i^2$，$R_3=\sum z_i^3$。三元组是下列中心化三次多项式的根再平移 $s/3$：
$$
 t^3-Q t/2-R_3/3,\qquad
 \Delta=\prod_{i<j}(z_i-z_j)^2=Q^3/2-3R_3^2 .
$$
令 $V_s(Q,R_3)$ 为该格内所有有序三元组的 $b_{r_1}b_{r_2}b_{r_3}$ 之和；$V_s^+$ 用各因子的模长代替。每格最多六项，故
$$
 \sum_{s,Q,R_3}|V_s^+(Q,R_3)|^2\le 6Z_1^3 .                         \tag{14}
$$
若两组的 $Q,\Delta$ 均相同，则 $R'_3=\pm R_3$。第一种给相同重集，第二种给 $\{r'_i\}=\{2s/3-r_i\}$。对 $R_3\mapsto -R_3$ 的置换用 Cauchy–Schwarz，并用 (14)，原点 $F(0,0)$ 展开中这整个区域的**逐项模长之和**至多
$$
                           12p Z_1^3\ll B_X.                          \tag{15}
$$
特别是，精确的重心反射也可覆盖六个互异频率。这里的频率 $r_i$ 是实际窗口输出的有限 Fourier 坐标，与第 5 页的反射中心 $c_i$ 有各自的定义。

将三次相关组成有限秩正算子 $\Gamma=p\sum_s V_s V_s^*$，作用在以 $(Q,R_3)$ 为坐标的 $\ell^2$ 空间上。有限 Fourier 正交性给出
$$
 \operatorname{Tr}\Gamma=\mathbb E_{u,v}F(u,v),\qquad
              \langle\mathbf1,\Gamma\mathbf1\rangle=F(0,0).
$$
第一式也可直接用重集计数，因为同格内所有乘积相同。第二式的常数向量未归一化，平方范数为 $p^2$。因此所缺的正是整张矩阵沿常数向量的上界。在 (15) 以外，需要控制不同方差或不同判别式的格子之间的带符号相关。



## 一个可以核验的 Fredholm 判据

<small>原稿第 12 页</small>

在窗口上取对角算子 $H_y=\operatorname{diag}(a_n)$。其非零奇异值与前稿的带窗卷积算子相同。置 $Y=X^{11/6}L^4$，$A=H_y^*H_y/Y$，$A$ 的特征值为 $\lambda_n=|a_n|^2/Y\ge0$。则
$$
                     \operatorname{Tr}(A^3)=M(y)/B_X .
$$
可以在一个固定的正谱参数上检测所需上界。三阶正则化行列式的实对数是 [6]
$$
 J=\log\det\nolimits_3(I+A)
   =\sum_n\big[\log(1+\lambda_n)-\lambda_n+\lambda_n^2/2\big].
$$
由于这里只涉及有限个特征值，直接微分标量函数即可。对 $\lambda\ge0$，
$$
 \frac{\lambda^3}{3(1+\lambda)}
 \le\int_0^\lambda\frac{t^2}{1+t}\,dt
 =\log(1+\lambda)-\lambda+\lambda^2/2
 \le\frac{\lambda^3}{3}.
$$
故 $0\le J\le\operatorname{Tr}(A^3)/3$。若 $J\le C$，则每个 $\lambda_n\ge1$ 都满足 $\lambda_n^2\le6C$。令 $K=\max(1,\sqrt{6C})$，再对标量下界求和得
$$
                 \operatorname{Tr}(A^3)\le3(1+K)C.                   \tag{16}
$$
因此 $\sup_y\log\det_3(I+A)\ll1$ 等价于目标。也可等价地控制正的预解式迹 $\operatorname{Tr}(A^3(I+A)^{-1})$。这里的行列式保留了特征值的大小；第 11 页的 $\Gamma$ 说明，已经控制的平均正迹与仍需估计的指定方向之间差在哪里。

**未决的连接。** 式 (1)、(13)、(15) 都使用真实的小弧系数。式 (12) 在四个独立素模数、单位参数和规定的共同权下给出幂次节省。当前推导尚未把剩下的远距离中心和或 $\Gamma$ 的常数方向化为一族满足 (12) 且总系数可控的和。哥德巴赫谱假设与原单侧目标仍未证得。



## 文献与形式化范围

<small>原稿第 13 页</small>

[1] [主弧与共振小弧](07-arcs.md)，式 (10)、(12)–(15) 及第 9 页的 Type I 块；[不相交零点](11-zeros.md)，式 (3)、(14)–(18)。

[2] F. Móricz，[A general moment inequality for the maximum of partial sums of single series](https://acta.bibl.u-szeged.hu/14837/1/math_044_fasc_001_002_067-075.pdf)，Acta Sci. Math. 44 (1982)。本稿第 4 页给出了所用四阶最大不等式的分块证明。

[3] É. Fouvry、E. Kowalski、Ph. Michel，[An inverse theorem for Gowers norms of trace functions over prime fields](https://arxiv.org/abs/1211.3282)。前稿所用平移 Legendre 例来自此类估计。

[4] T. Cochrane、C. Pinner，[Using Stepanov’s method for exponential sums involving rational functions](https://www.math.ksu.edu/~cochrane/research/stepmix.pdf)，引言与对极点阶数的说明。式 (11) 的两个有限极点均为简单极点。

[5] J. Wu、P. Xi，[Arithmetic exponent pairs for algebraic trace functions and applications](https://arxiv.org/abs/1603.07060)。本稿第 9 页写出了一个适用于当前四因子的单次差分证明。

[6] M. Bertola、M. Cafasso，[正则化 Fredholm 行列式的定义](https://spectrum.library.concordia.ca/id/eprint/976937/1/bertola2012d.pdf)，附录 B。式 (16) 完全由有限维标量不等式推出。

[7] É. Fouvry、E. Kowalski、Ph. Michel，[Algebraic trace functions over the primes](https://people.math.ethz.ch/~kowalski/weights-over-primes.pdf)，定理 1.5 与推论 1.12。

**Lean 4 核验。** 配套文件在 Lean 与 mathlib 4.19.0 中核验乘法特征的完全平移相关、混合第四矩的二点刚性、反射权均方、图叶子与最后一条边的不等式、按周期分组的 Cauchy–Schwarz、三次幂和的重集恢复、中心化判别式及预解式的谱上界等引理。文件对声明的传递公理依赖作了检查。连续圆法输入、特征平均与全部渐近估计的组合见正文。
