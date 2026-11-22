# 哥德巴赫六阶矩的五模数项

<small>原稿第 1 页</small>

设 $L=\log(2X)$，假设 Dirichlet $L$ 函数满足 GRH。沿用等宽主弧 $q\le Q=\lfloor X^{3/10}\rfloor$、半宽 $L^4/X$，其补集为 $\mathfrak m$。对锐前缀 $P_y(\alpha)=\sum_{m\le y}\Lambda(m)e(m\alpha)$ 取宽度 $X^{4/5}$ 的上端平滑。下文的谱子和使用这个平滑版本，常数对 $0\le y\le2X$ 一致。$e(t)=\exp(2\pi i t)$。

**五模数定理。** 在六个频率位置各取两条素数腿的非平凡零点留数。若两侧模数分别为 $\{p,u_1,u_2\}$ 和 $\{p,v_1,v_2\}$，五个模数各异，且公共模数 $p$ 的两枚正标签与两枚负标签完全匹配，则这部分的带符号贡献满足
$$
               \boxed{\displaystyle\sup_y |Z_{\rm five}(y)|
                         \ll X^{11/2}L^{11}.}                         \tag{1}
$$
这里的 $p$ 是任意正整数模数。结果覆盖所有非平凡零点，包括重零点，也允许原六重积分域 $\Omega_X$ 的截边。前稿对此配置的周期余项界为 $O_\varepsilon(X^{6+\varepsilon})$。[1]

**全部两匹配定理。** 记 $Z_{\ge2}$ 为按重集比较，至少两对跨侧标签 $(q,\chi,\gamma)$ 一一匹配的双零点子和。对原分母范围 $q\le\lfloor\sqrt X/L\rfloor$ 有
$$
                \sup_y|Z_{\ge2}(y)|\ll X^{11/2}L^{11}.                \tag{2}
$$
证明先将四个自由位置恢复为同一频率上的函数，再对公共模数的配对保留特征相位。其余匹配形状通过容斥处理。展开的符号保留到每个独立的零点和或配对核已形成。

**移线的另一个结论。** 若两个素数和都只绕分母一展开，原锐截点的单侧目标可等价地写成只含 $\zeta$ 非平凡零点的完整六阶矩上界，见末两页。这是一种不同的展开。式 (1)、(2) 在多模数展开中成立。原目标 $\sup_y\operatorname{Re}\mathcal J_y\ll X^{11/2}L^{12}$ 仍未证得。



## 素数和的显式公式

<small>原稿第 2 页</small>

第一条腿取 $f_y(t)=w_0(t)\int_0^1\rho(v)\mathbf1_{t\le y-\delta v}\,dv$，$\delta=X^{4/5}$，$\rho$ 为固定光滑概率密度，支撑在 $(0,1)$。取固定光滑 $w_0$，在 $t\le a$ 为零、在 $t\ge b$ 为一，其中 $1<a<b<2$。因 $\Lambda(1)=0$，这一约定给出原前缀的同一平滑算术和。第二条腿取 $g(t)=\eta(t/X)$，其中固定实权 $\eta$ 紧支撑于正半轴且 $|\widehat\eta(\xi)|\ll e^{-c\sqrt{|\xi|}}$。[1] 对其中任一权 $w$ 写
$$
 P_w(\alpha)=\sum_n\Lambda(n)w(n)e(n\alpha),\qquad
 F_w(s,\beta)=\int_0^\infty w(t)e(\beta t)t^{s-1}dt .
$$
选可测 Dirichlet 逼近 $\alpha=a_0/q+\beta$，$(a_0,q)=1$，$q\le D=\lfloor\sqrt X/L\rfloor$，$|\beta|\le1/(qD)$。对每个 $\chi\bmod q$ 用诱导它的原始特征 $\chi^*$ 写显式公式。单位类展开的系数为 $\chi(a_0)\tau(\bar\chi)/\varphi(q)$，其 Gauss 和满足 $|\tau|\le\sqrt q$。在 $\Re s>1$ 上对 $(-L'/L)(s,\chi^*)F_w(s,\beta)$ 积分。从极点和非平凡零点得到
$$
\begin{aligned}
 P_w(\alpha)&=M_w(\alpha)+Z_w(\alpha)+E_w(\alpha),\\
 M_w&=\frac{\mu(q)}{\varphi(q)}F_w(1,\beta),\\
 Z_w&=-\frac1{\varphi(q)}\sum_{\chi\bmod q}\chi(a_0)\tau(\bar\chi)
           \sum_{\rho_\chi}m_{\rho_\chi}F_w(\rho_\chi,\beta),\\
 |E_w|&\ll (1+\sqrt q)L^2 . 
\end{aligned}                                                       \tag{3}
$$
内和按不同非平凡零点取，$\rho_\chi=1/2+i\gamma$。主特征的 Gauss 和为 $\mu(q)$。原始与非原始特征在素数幂处的差，以及原加法和中的非单位项，只涉及底数整除 $q$ 的素数幂。它们的 $\Lambda$ 质量对每条特征至多 $O(L\omega(q))$。先乘 Gauss 权再求和的成本至多 $O(\sqrt q L^2)$。平凡零点与移线由下一页控制。[2]

**小弧上的单枚留数。** 固定一个 $\zeta$ 非平凡零点 $\rho$。函数 $J(u)=\int\eta(x)x^{\rho-1}e(ux)dx$ 是非恒零整函数，由 Fourier 唯一性可取固定 $0<u<1$ 使 $J(u)\ne0$。令 $q$ 沿素数增长，取 $X=q^{5/2}$ 及 $\alpha=1/q+u/X$。它距任一主弧中心至少 $1/(qQ)-u/X\gg L^4/X$。对任一不同的既约分数 $b'/s$、$s\le D$，相同的间距界 $1/(qs)-u/X>1/(sD)$ 还保证所选逼近唯一。模 $q$ 主特征诱导自 $\zeta$，Gauss 和为 $-1$。光滑腿的该枚留数模长恰为 $m_\rho\sqrt X\,|J(u)|/(q-1)\asymp X^{1/10}$。这给出原小弧上必须通过求和处理的单项。



## 哪一部分可以任意次幂衰减

<small>原稿第 3 页</small>

取整数 $J\ge1$，把积分线移至 $\sigma=-J-1/2$。原始 $L$ 函数的函数方程、对数导数在 $\Re(1-s)>1$ 的绝对收敛和 Gamma 函数的反射公式给
$$
 \left|\frac{L'}L(-J-1/2+it,\chi^*)\right|
       \ll \log(2q(J+|t|+2)).
$$
半整数线与全部 Gamma 极点有固定距离。由 $u=\log x$ 变元分部积分两次，$F_w$ 在此线满足
$$
 |F_w(-J-1/2+it,\beta)|
    \ll \frac{a^{-J}(1+J+X)^2 L}{1+t^2},\qquad |\beta|\le1/2 .
$$
隐常数对 $J,X,y$ 一致。支撑在 $x\ge a>1$ 产生 $a^{-J}$，对 $e(\beta x)$ 的两次求导已计入。固定 $q,X,J$，取避开零点纵坐标的高度趋向无穷，水平边由 Mellin 快速衰减趋零。可用单位高度零点数 $O(\log(2q(2+|t|)))$ 和对数导数的局部展开选择这些高度。[2,3]

于是给定 $A>0$，取 $J\ge C_A L$ 可令新直线积分为 $O_A(X^{-A})$，也可令 $J\to\infty$。穿过的平凡零点在 $s=-k$。它们的留数绝对和由
$$
 C\int_a^{CX}\frac{dx}{x(1-x^{-1})}\ll L
$$
控制。用到 $\sum_{k\ge0}x^{-k}=(1-x^{-1})^{-1}$，含 $\zeta$ 时只取实际存在的平凡零点。对每条原始特征，这就完成了 (3)。固定 $X$ 时 $F_w(1/2+i\gamma,\beta)$ 对高度快速衰减，故非平凡零点和绝对收敛。

非平凡零点则留下 $-m_\rho F_w(\rho,\beta)$。尺度 $S$ 上这一项含 $S^{1/2+i\gamma}$。GRH 给出实部 $1/2$。式 (1) 的证明通过求和来利用其振荡。若从 Vaughan Type II 级数识别这些临界线留数，则每枚仍有相同的 $-m_\rho$ 系数。[1] 其自由位置的留数之和可由真正素数和的 (3) 恢复，因此下文无需对整个 Type II 级数做深移线。

在多模数展开本身，含 $E_w$ 的误差也可在完整系数范数中移去。两乘积之差为 $E_{f_y}P_g+(P_{f_y}-E_{f_y})E_g$。由 (3)、$q\le D$ 和 $\|P_w\|_2\ll\sqrt{XL}$，在小弧上它的 $L^2$ 范数至多 $O(X^{3/4}L^{5/2})$。用 Parseval 和 $\ell^6\le\ell^2$ 即得到同阶的带窗六阶范数界。



## 四个自由模数先作两两卷积

<small>原稿第 4 页</small>

写 $B\asymp1+X|\beta|$，各符号的完整二进区间 $I_B$ 长 $\asymp B/X$。由 Dirichlet 逼近得 $qB\le H=C X/D$。每个 $\alpha$ 已选唯一的 $q$。若一个位置的两枚标签均不受相等条件约束，则它们的和在 $\alpha$ 处恰为
$$
 G(\alpha)=\mathbf1_{\mathfrak m}(\alpha) Z_{f_y}(\alpha)Z_g(\alpha).
$$
对真实素数和，由 Parseval 和 $\sum_{n\le CX}\Lambda(n)^2\ll XL$ 有 $\|P_w\|_2\ll\sqrt{XL}$。主极点项在各分母上放宽至全部既约分子和整条 $\beta$ 实轴，再用 Plancherel，得 $\|M_w\|_2^2\ll X\sum_{q\le D}1/\varphi(q)\ll XL$。式 (3) 的余项在此范围为 $O(X^{1/4}L^2)$。因此 $\|Z_w\|_2\ll\sqrt{XL}$。

对固定光滑腿，在 (3) 中用驻相界 $|F_g(1/2+i\gamma,\beta)|\ll\sqrt{X/B}$ 及 $|\gamma|\le C_1 B$ 的零点数 $O(BL)$。更高处用非驻相分部积分，见第 6 页。于是 $\|Z_g\|_\infty\ll\sqrt{qXB}\,L\ll X^{3/4}L^{3/2}$，前一界按所在分母理解。因此
$$
          \|G\|_1\ll XL,\qquad \|G\|_2^2\ll X^{5/2}L^4 .              \tag{4}
$$
令 $D_W(t)=\sum_{n\in2\mathbb Z}W(n/X)e(-nt)$。Poisson 求和给 $\|D_W\|_1\ll1$。固定两个已匹配位置的平移 $v$。四个自由位置的积分一致满足
$$
 \int_{\mathbb T^4}|D_W(v+\textstyle\sum_{i=1}^4\epsilon_i\alpha_i)|
          \prod_{i=1}^4 |G(\alpha_i)|\,d^4\alpha
 \ \le\ \|D_W\|_1\,\|G\|_2^2\|G\|_1^2
 \ \ll X^{9/2}L^6.                                                     \tag{5}
$$
固定一对的和或差，该对的相关由 Hölder 的 $(2,2)$ 界至多为 $\|G\|_2^2$。余下两位置各作一次 $L^1$ 积分。自由模数互异、避开 $p$ 和 $\Omega_X$ 都是频率条件，它们在各自零点和合成后可被模长一放宽。此顺序保留了原来因逐分母取模而丢掉的相位。



## 公共模数上一枚已经配对的标签

<small>原稿第 5 页</small>

为统一两条腿，把单个 Mellin 因子归一化为
$$
 v_w(\gamma,\beta)=\sqrt B\,X^{-1/2-i\gamma}F_w(1/2+i\gamma,\beta).
$$
对两种物理权，所有高度都有 $|v_w|\ll1$。平滑腿由一、二阶导数检验得到。前缀的总变差一致有界，可由分部求和归结为任意截点 $T$ 的估计
$$
 \sup_{T>0,\,\gamma\in\mathbb R}
    \left|\int_0^T t^{-1/2+i\gamma} e^{\pm it}dt\right|\ll1 .
$$
证明取 $A=|\gamma|\ge1$。在 $t\asymp A$ 作二阶导数检验，振幅 $A^{-1/2}$ 与所得 $A^{1/2}$ 相消。在 $t\asymp U<A/2$ 用一阶导数 $\gg A/U$，各段界 $O(\sqrt U/A)$。在 $U>2A$ 用一阶导数 $\gg1$，各段界 $O(U^{-1/2})$。两端均是可求和的几何级数。$A<1$ 时在 $t\le 3$ 绝对积分，其余同理。将 $t$ 缩放为 $2\pi X|\beta|x$ 即得所需界。$B\asymp1$ 用平凡界即可。

考虑模数相同的两位置，偏移尺度为 $B,B'$。符号相反时特征只以 $\chi(a_0)\overline{\chi(a'_0)}$ 进入同一标签的配对。固定另一端的 $(a'_0,\beta')$，把其中的一个 Gauss 比率、$m_\gamma$、$v_{w'}$ 和单位模因子并入权 $b_{\chi,\gamma}$。有 $|b_{\chi,\gamma}|\ll L$。对 $|\gamma|\le X^2$，重数界来自单位高度的零点数。对 $|\gamma|>X^2$，平滑权在 $\log t$ 上分部积分足够多次，导数成本每次至多 $O(1+X)$，足以吸收重数的对数增长。

余下端的归一化特征和可写为
$$
 F_w^b(a_0,\beta)=\sum_{\chi\bmod p}\chi(a_0)
    \frac{\tau(\bar\chi)}{\sqrt p}\sum_{\gamma}m_\gamma b_{\chi,\gamma}v_w(\gamma,\beta).
$$
吸收入 $b$ 的固定相位可随 $\chi,\gamma$ 而变。所需均方对这些选择一致。参考端也可取负侧，复共轭不改变界。



## 精确计算偏移均方的对数

<small>原稿第 6 页</small>

记 $\mathbb E$ 为模 $p$ 单位分子和 $I_B$ 上的归一化平均。在上页的 $|b_{\chi,\gamma}|\ll L$ 条件下，
$$
 \|F_{f_y}^b\|_{L^2(\mathbb E)}\ll\sqrt{\varphi(p)B}\,L^3,\qquad
 \|F_g^b\|_{L^2(\mathbb E)}\ll\sqrt{\varphi(p)B}\,L^2.                \tag{6}
$$
证明先固定特征、取物理二进尺度 $S\le CX$，记 $Z=\max(1,SB/X)$。将物理变量换为 $u=t/S\asymp1$，单块的局部归一化为 $\sqrt Z$ 乘
$$
 V(\gamma,\beta)=\int k(u)u^{-1/2+i\gamma}e(S\beta u)du .
$$
对 $|\gamma|\le C_1 Z$，先合成 $A(z)=\sum m_\gamma b_{\chi,\gamma}S^{i\gamma}e^{i\gamma z}$。取固定光滑非负上界覆盖 $\log u$ 支撑，展开平方。傅里叶核以 $(1+|\gamma-\gamma'|)^{-2}$ 衰减，每一行按重数求和为 $O(L)$，且全部重数 $\ll ZL$。故固定对数区间上 $\int |A(z)|^2 dz\ll ZL^4$。在 $\beta$ 上用实轴 Plancherel 并除以 $|I_B|\asymp Z/S$，得局部归一化后的均方根 $\ll\sqrt Z L^2$。$SB/X<1$ 时 $Z=1$，用单位高度的计数即可。

对 $C_1 Z<|\gamma|\le X^2$，有界变差给 $|V|\ll1/|\gamma|$。每个二进高度段的 $\sum m_\gamma/|\gamma|\ll L$，总和 $\ll L^2$。乘权 $b$ 和局部归一化，成本至多 $\sqrt Z L^3$。对固定光滑的 $g$，相位一阶导数 $\gg|\gamma|$，更高阶导数 $O_j(|\gamma|)$，故 $|V|\ll_N(1+|\gamma|)^{-N}$。相应成本降至 $O(\sqrt Z L^2)$。超过 $X^2$ 的平滑尾可取任意负幂。上述证明也允许删去给定的纵坐标。

将 $S$ 块从局部归一化换回 $v_w$，需乘模长 $\sqrt{BS/(XZ)}$ 的因子。局部均方根中的 $\sqrt Z$ 正好消去，$\sum_{S\ {\rm dyadic}}\sqrt{S/X}\ll1$。因此移动前缀不会额外损失一个 $L$。最后对单位分子用特征 Parseval，得到 (6)。其中的对数来自零点数、重数和前缀远端高度之和。



## 公共模数的两个尺度可以直接求和

<small>原稿第 7 页</small>

先指定公共位置两枚标签的一种匹配置换。固定尺度较大的一端，在较小的 $B_0=\min(B,B')$ 一端使用 (6)。两条配对特征和共用同一采样点，用 Hölder 得归一化乘积的平均至多 $C\varphi(p) B_0 L^5$。无论匹配是否交换两种物理权，取平均的一端总有一条前缀腿和一条固定光滑腿。

两种置换所描述事件的重叠要求四个标签全等。此时用较小端的光滑腿计数，其余三个归一化积分用一致界。对每个特征，$|\gamma|\le C_1 B_0$ 有 $\sum m_\gamma^4\ll B_0L^4$。其余高度由光滑腿的非驻相衰减处理。因此交集的归一化贡献至多 $C\varphi(p) B_0 L^4$。按两次相加、一次相减计数，恰得到重集匹配事件。

每个端点在还原归一化后带 $pX/(\varphi(p)^2 B)$，另一端用 $B'$。分子个数 $\varphi(p)^2$ 与偏移面积 $O(BB'/X^2)$ 一并计入。于是固定 $p,B,B'$ 的绝对积分至多
$$
             C\,\frac{p^2}{\varphi(p)}\min(B,B')\,L^5 .                \tag{7}
$$
两个尺度上界均为 $O(H/p)$。对 $B=2^i,B'=2^j$ 用恒等式
$$
 \sum_{0\le i,j<n}\min(2^i,2^j)=3(2^n-1)-2n.
$$
它可按最大的行、列作归纳。两重尺度求和只花 $O(H/p)$。最后由 $n/\varphi(n)=\sum_{d\mid n}\mu^2(d)/\varphi(d)$ 以及收敛乘积 $\prod_\ell(1+1/(\ell(\ell-1)))$，有 $\sum_{p\le D}p/\varphi(p)\ll D$。同一恒等式也给第 4 页的 $\sum_{p\le D}1/\varphi(p)\ll L$。故匹配核的两个频率变量及模数的总质量至多
$$
             C H L^5\sum_{p\le D}\frac p{\varphi(p)}
                  \ll H D L^5\ll X L^5 .                              \tag{8}
$$
把 (8) 乘 (5)，得到 $X^{11/2}L^{11}$。这证明 (1)，并为所求的 $L^{12}$ 保留一个对数。上述估计也适用于指定一种置换的事件和单独的全等交集。



## 两对标签分布在三个或四个频率位置

<small>原稿第 8 页</small>

先只指定两条跨侧等式，四个标签位置互不重复。若它们仅占两个频率位置，上页的每种置换均适用，其余四个位置用 (5)。这也容许额外的、只依赖频率或所选分母的限制。以下两种形状有严格的幂次余量，固定次对数可收入 $X^\varepsilon$。

**占三个位置。** 两条边有一个公共频率位置，三处模数都为 $p$。把中心的两个分子相位和偏移当作已给定的数据。在每个外端，一条腿与中心配对，另一条腿自由。由 (6) 和同一估计的 $b=1$ 版本，对该端的归一化乘积取平均至多 $O(pB L^C)=O(HL^C)$。两外端独立，中心已无自由求和。每处还原归一化并积分、求分子后产生的比率至多 $(p/\varphi(p))^{O(1)}$，可吸入 $X^\varepsilon$。于是三个位置合计质量
$$
               \ll_\varepsilon D H^2 X^\varepsilon
               \ll_\varepsilon X^{3/2+\varepsilon}.
$$
余下三个自由位置在任意平移上的核积分 $\ll\|D_W\|_1\|G\|_2^2\|G\|_1\ll X^{7/2}L^5$，故这种形状至多 $O_\varepsilon(X^{5+\varepsilon})$。

**占四个位置。** 对其中一条边，两个端点各另有一条自由腿。令 $K_{12}$ 为已配对标签的归一化和，$F_1,F_2$ 为另两条腿各自的自由和。条件于第二端，用 (6) 得 $\|K_{12}\|_{L^2(1,2)}\ll\sqrt H L^C$。另外，$\|F_1F_2\|_{L^2(1,2)}=\|F_1\|_2\|F_2\|_2\ll HL^C$。这里 $L^2(1,2)$ 使用两个端点的乘积概率测度。故一条边连同两条自由腿，计入公共模数的和，积分质量至多 $D H^{3/2} X^\varepsilon\ll X^{5/4+\varepsilon}$。另一条边有同样界。若两边模数相同，取模后放宽该限制仍适用。最后两个自由位置承担 $\|D_W\|_1\|G\|_2^2\ll X^{5/2}L^4$。合计仍为 $O_\varepsilon(X^{5+\varepsilon})$。

这三个估计使用指定等式的整块带符号和。为了得到“至少两对”的结论，还须处理多种指定方式的交集。



## 容斥交集中的重复标签

<small>原稿第 9 页</small>

至少两对匹配是有限多个事件的并，每个事件指定两条不共用标签位置的跨侧等式。用容斥准确计算其指标。每个交集只施加等式，不施加不等式。对固定模数形状，选每个模数上频率位置较少的一侧为参考，平手选正侧。参考位置总数 $h=\sum_q\min(s_q^+,s_q^-)$。有两对匹配要求 $h\ge1$。$h=3$ 时两侧模数多重集相同，前稿对整个 $Z^{\rm bal}_{\ge2}$ 已有 $O_\varepsilon(X^{21/4+\varepsilon})$ 的界。[1]

在 $h=1,2$ 时，记交集中被等式涉及的参考、非参考标签出现次数分别为 $a,b$，由这些等式生成的非单点等价类数为 $c$。每个等价类在两侧都有标签，所以 $a,b\ge2$，$c\le\min(a,b)$。不要求不同等价类取得不同的数值。固定参考标签后，非参考侧有 $12-2h-b$ 枚标签独立自由。参考侧只需选择 $2h-a+c$ 个初始标签值。

引用前稿式 (12) 的分子网格估计。令 $K$ 为参考模数的最小公倍数。对固定六个模数和偏移块，含 $X^\varepsilon$ 的上界为
$$
 \left(1+\frac XK\right)
       H^{\,2h-a+c+(12-2h-b)/2}\,X^\varepsilon .                      \tag{9}
$$
理由是每个独立参考值按绝对和至多花费 $HL^C$，指定的再现用一致的 $L^C$ 界，每个自由非参考标签用均方花费 $\sqrt H L^C$。在参考分子上放宽互素性后，带符号的分数和均匀覆盖 $K^{-1}\mathbb Z/\mathbb Z$。平均 $|D_W|$ 再积分一个参考偏移，至多花费 $1+X/(K B_A)\le1+X/K$。这里可将物理、偏移二进块数和固定次对数一并吸收。式 (7) 的临界对数估计另已完成。

若 $h=2$，有两个参考模数和两个额外模数可变。因 $\sum_{p_1,p_2\le D}1/[p_1,p_2]\ll_\varepsilon X^\varepsilon$，(9) 中括号的模数总和至多 $O_\varepsilon(X^{2+\varepsilon})$。$H$ 的指数为 $8-(a-c)-b/2$。只要 $2(a-c)+b\ge3$，总计至多 $X^{21/4+\varepsilon}$。余下的唯一可能是 $a=b=c=2$，恰为上页及第 7 页已处理的两条独立等式。



## 不平衡模数的最后一种交集

<small>原稿第 10 页</small>

设 $h=1$。两侧只有一个共同模数 $p$，一侧仅有一个该模数的位置，另一侧有 $t=1,2,3$ 个。两枚参考标签都被涉及，$a=2$，且 $b\le2t$。除 $p$ 以外至多有 $5-t$ 个可变模数。在 (9) 中对 $1/p$ 求和，得到
$$
 \ll_\varepsilon
      X^\varepsilon H^{\,c+5-b/2}D^{\,5-t}(D+X).                      \tag{10}
$$
若 $b\ge3$，必有 $t\ge2$，而 $c\le2$。式 (10) 至多为 $X^{21/4+\varepsilon}$。若 $b=2,c=2$，恰为两条独立等式。若 $b=2,c=1$，四个涉及的标签全等。$t\ge2$ 时 (10) 至多为 $X^{5+\varepsilon}$。$t=1$ 时四个标签落在两个位置，第 7 页的全等交集界适用。

至此，每个容斥交集均为 $O(X^{11/2}L^{11})$ 或 $O_\varepsilon(X^{21/4+\varepsilon})$。标签位置只有十二个，容斥系数绝对值总和有绝对常数界。取固定 $\varepsilon<1/4$，得到式 (2)。在原来的多模数展开中，完整双零点和还含零对匹配和恰好一对匹配的部分。

**谱大筛的适用位置。** 直接对四个自由位置的 $a_i/q_i$ 展开 Poisson 核，得到共同频率 $n$ 上的 $e(-n\sum_i\epsilon_i a_i/q_i)$。合成前，每个分子的算术因子是模 $q_i$ 的特征值。固定 $n$ 并补全某个单分子时，相应和是 Gauss 型，几何截边还可能破坏补全。另一个对偶展开确有 $S(k,(n-j)h;q)$，但要把两种展开接在一起，需给出同一模数变量、两个 Kloosterman 参数及所用光滑权的导数界。Deshouillers–Iwaniec 型大筛定理对倒数相位和权的依赖有具体假设。[4]

式 (5) 用一个共同的加法核把两对自由位置联系起来。式 (6) 在共同模数的特征以及 Mellin 高度上同时取均方。这两处给出了 (1) 所需的抵消。平均的次序还允许保留不光滑的 $\Omega_X$ 截边。



## 用分母一单独处理主极点

<small>原稿第 11 页</small>

现在在整个小弧上对**两条腿**统一用分母一展开，取 $\beta\in[-1/2,1/2]$ 表示 $\alpha$。记 $Z_w^{(1)}$ 为式 (3) 中相应的 $\zeta$ 非平凡零点和，$V_w=F_w(1,\beta)$。这样 (3) 成为 $P_w=V_w+Z_w^{(1)}+E_w^{(1)}$，误差 $O(L)$。由 $q=1$ 主弧排除的区间，小弧上 $|\beta|\ge L^4/X$。因此
$$
 |V_g|\ll X e^{-c\sqrt{X|\beta|}}=O_A(X^{-A}),\qquad
 |V_{f_y}|\ll \min(X,|\beta|^{-1}) .                                  \tag{11}
$$
第二式只用一致有界变差。主极点实际产生这两个 Fourier 积分。对移动前缀，需要继续估计它在小弧上的乘积。

在原来的多模数图上已经得到 $\|Z_g\|_\infty\ll X^{3/4}L^{3/2}$。若选定的 $q\le Q$，小弧上 $|M_g|\ll_A X^{-A}$。若 $q>Q$，则 $|M_g|\ll X/\varphi(q)\ll X^{3/4}$，用 $q/\varphi(q)\ll L$ 和 $Q=X^{3/10}+O(1)$ 的严格幂次余量。结合 (3) 有 $\sup_{\mathfrak m}|P_g|\ll X^{3/4}L^{3/2}$。这个关于真实素数和的界可以在任一展开中使用。

置 $U=\mathbf1_{\mathfrak m} V_{f_y}P_g$。由 (11) 积分 $|\beta|^{-1}$ 和 $|\beta|^{-2}$，分别得
$$
 \|\widehat U\|_\infty\le\|U\|_1\ll X^{3/4}L^{5/2},\qquad
 \sum_n|\widehat U(n)|^2=\|U\|_2^2\ll X^{5/2}L^{-1}.
$$
第二式保留了 $\int_{L^4/X}^{1/2}\beta^{-2}\,d\beta\le X/L^4$。用第一式的四次方乘第二式，并限制至偶数及有界窗 $W$，给出
$$
     \boxed{\ \sum_{n\in2\mathbb Z}W(n/X)|\widehat U(n)|^6
                 \ll X^{11/2} L^{9} .\ }                               \tag{12}
$$
其余误差乘积在完整带窗系数的 $\ell^6$ 范数下为 $O(\sqrt X L^C)$。这是由 $\ell^6\le\ell^2$，(3)、(11) 及 $\|P_g\|_2+\|Z_{f_y}^{(1)}\|_2\ll\sqrt{XL}$ 得到。后一个范数还用到实轴 Plancherel 给 $\|V_{f_y}\|_2\ll\sqrt X$。



## 原单侧问题的零点判据

<small>原稿第 12 页</small>

对 $\mathbb T$ 上函数 $F$ 记
$$
 \mathcal N(F)=
 \left(\sum_{n\in2\mathbb Z}W(n/X)|\widehat F(n)|^6\right)^{1/6}.
$$
在第 11 页的分母一展开中，令 $Y_y=\mathbf1_{\mathfrak m}Z_{f_y}^{(1)} Z_g^{(1)}$。展开乘积差，
$$
 \mathbf1_{\mathfrak m}P_{f_y}P_g-Y_y
   =U+\mathbf1_{\mathfrak m}E_{f_y}^{(1)}P_g
     +\mathbf1_{\mathfrak m}Z_{f_y}^{(1)}(V_g+E_g^{(1)}).
$$
由 (12) 和三角不等式，$\mathcal N$ 下的差为 $O(X^{11/12}L^{3/2})$。前稿证明了两条转移估计。第一，原锐前缀换成当前宽 $\delta=X^{4/5}$ 的平滑前缀，完整带窗范数的差为 $O(X^{11/12}L^2)$。第二，原锐前缀的完整带窗六次方，与限制在 $\Omega_X$ 的 $\operatorname{Re}\mathcal J_y$ 相差 $O(X^{11/2}L^{12})$。[1] 因而
$$
 \sup_y\operatorname{Re}\mathcal J_y\ll X^{11/2}L^{12}
 \quad\Longleftrightarrow\quad
 \sup_y \mathcal N(Y_y)^6\ll X^{11/2} L^{12}.                         \tag{13}
$$
右边仍须控制不同零点之间的相关。第 1 至 10 页的模数匹配分类采用 $q\le D,\ qB\le H$。在分母一覆盖整圆时，$B$ 可以达到 $X$。因此 (2) 与 (13) 各有自己的零点展开。将多模数的匹配估计用于式 (13) 还需要证明两种展开之间的转移界。

### 文献与核验

[1] [多模数匹配与联合均方](09-labels.md)，式 (7)、(12)、(17)。[Mellin 分解与截点转移](08-mellin.md)，式 (9)、(10)。[圆法积分与 $\Omega_X$](07-arcs.md)，式 (10) 至 (15)。

[2] Helfgott，[Major arc bounds](https://webusers.imj-prg.fr/~harald.helfgott/anglais/PartIVapril1.pdf)，第 16 章的扭转显式公式。[NIST DLMF §25.15](https://dlmf.nist.gov/25.15)，原始特征的函数方程与平凡零点。

[3] Bennett、Martin、O’Bryant、Rechnitzer，[Counting Zeros of Dirichlet $L$-Functions](https://arxiv.org/abs/2005.02989)。导数检验和式 (6) 的核估计已在正文展开。

[4] Deshouillers、Iwaniec，[Kloosterman sums and Fourier coefficients of cusp forms](https://doi.org/10.1007/BF01390728)。[Drappeau，定理 1](https://drappeau.perso.math.cnrs.fr/documents/hdr-eng.pdf) 给出倒数相位和光滑性假设。

配套 Lean 4.19.0 文件核验有限群卷积换元、Haar 测度下平移相关的 Hölder 界、物理尺度的归一化、二进尺度和、两对匹配时的容斥计数和指数运算。显式公式、连续零点均方与 (1) 至 (13) 的整体推导见正文。
