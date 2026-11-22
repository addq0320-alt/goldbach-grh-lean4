# 哥德巴赫六阶矩中的自由特征和

<small>原稿第 1 页</small>

假设所有 Dirichlet $L$ 函数满足 GRH。在六阶矩的六个积分位置，各取两个来自临界线非平凡零点的留数。在取共轭前比较正、负两侧各六个标签 $(q,\chi,\gamma)$。用 $Z_{\ge k}(y)$ 表示至少有 $k$ 对可以一一匹配时，这些项的**带符号积分之和**。一枚标签在一个位置只能匹配一次。解析重数随留数计入系数。

**定理。** 设 $L=\log(2X)$。对原锐截点的驻相高度带，或对宽 $X^{4/5}$ 的平滑截点及全部非平凡零点，对任意固定 $\varepsilon>0$ 一致有
$$
\begin{aligned}
 \sup_{0\le y\le2X}|Z_{\ge6}(y)|&\ll_\varepsilon X^{9/2+\varepsilon},&
 \sup_y|Z_{\ge5}(y)|&\ll_\varepsilon X^{19/4+\varepsilon},\\
 \sup_y|Z_{\ge4}(y)|&\ll_\varepsilon X^{5+\varepsilon},&
 \sup_y|Z_{\ge3}(y)|&\ll_\varepsilon X^{21/4+\varepsilon}.
\end{aligned}                                                     \tag{1}
$$
这些界允许两侧的模数多重集不同。若两侧的模数多重集相同，还能对 $k=1,2$ 证明 $\sup_y|Z^{\rm bal}_{\ge k}(y)|\ll_\varepsilon X^{21/4+\varepsilon}$。所有隐常数允许依赖固定权函数。

**积分的定义。** 记 $e(t)=\exp(2\pi i t)$，$P_y(\alpha)=\sum_{m\le y}\Lambda(m)e(m\alpha)$，$P_\eta(\alpha)=\sum_j\Lambda(j)\eta(j/X)e(j\alpha)$。固定光滑权 $\eta,W$ 紧支撑于正半轴，$W$ 在 $[1,2]$ 为一。前三个位置取正号，后三个位置取负号。写 $\Delta=\sum_i\epsilon_i\alpha_i$，
$$
 D_W(v)=\sum_{n\in2\mathbb Z}W(n/X)e(-nv),\qquad H_y=\mathbf1_{\mathfrak m}P_yP_\eta .
$$
原积分 $\mathcal J_y$ 在 $\Omega_X\subset\mathfrak m^6$ 上将前三个 $H_y$ 与后三个 $\overline{H_y}$ 相乘，再乘 $D_W(\Delta)$ 积分。这里 $\Omega_X$ 是集体半整数共振、至多一条微观边的原积分域。[1] 下文的界对任意只依赖六个频率、模长至多一的截取权都成立。式 (1) 控制其中的双零点项，原单侧目标为 $X^{11/2}L^{12}$。



## 局部展开与两个尺度

<small>原稿第 2 页</small>

小弧 $\mathfrak m$ 是分母 $q\le\lfloor X^{3/10}\rfloor$ 的等宽主弧的补集，主弧半宽 $L^4/X$。固定一个可测的 Dirichlet 逼近选择 $\alpha=a/q+\beta$。设
$$
 \begin{gathered}
 D=\lfloor\sqrt X/L\rfloor,\qquad q\le D,\qquad |\beta|\le 1/(qD),\\
 B\asymp1+X|\beta|,\qquad qB\le H=C\sqrt X\,L .
 \end{gathered}                                                       \tag{2}
$$
$B$ 为二进尺度。每一符号的偏移块可嵌入长 $\asymp B/X$ 的标准区间 $I_B$，实际弧的截边留在原权内。以光滑二进分割将第一条腿切至物理尺度 $M$，其中 $1\le M\ll X$，第二条腿的尺度为 $X$。令 $S=M$ 或 $X$，$Z=\max(1,SB/X)$。缩放后的权 $g(x)$ 支撑在固定的 $0<c\le x\le C'$，上确界与总变差一致有界。

对模 $q$ 的单位类展开。记 $U_q=(\mathbb Z/q\mathbb Z)^\times$，$\tau(\bar\chi)=\sum_{b\bmod q}\bar\chi(b)e(b/q)$。既约分子的 Gauss 系数为 $\chi(a)\tau(\bar\chi)$。加法 Parseval 给全部分子的平方和 $q\varphi(q)$，而单位分子的模相同，故 $|\tau(\bar\chi)|\le\sqrt q$。记 $\rho=1/2+i\gamma$ 为非平凡零点，$m_\gamma$ 为它在该特征下的重数。置
$$
 V_\beta(\gamma)=\int g(x)x^{-1/2+i\gamma}e(S\beta x)\,dx,\qquad
 c_{\chi,\gamma}(\beta)=-\frac{\tau(\bar\chi)}{\sqrt q}\,
 S^{i\gamma}m_\gamma\sqrt Z\,V_\beta(\gamma).                         \tag{3}
$$
这条腿的留数项恰为 $[\sqrt{qS}/(\varphi(q)\sqrt Z)]\,\chi(a)c_{\chi,\gamma}(\beta)$。一个位置的两个确定因子的乘积满足
$$
 \frac q{\varphi(q)^2}\frac{\sqrt{MX}}{\sqrt{\max(1,MB/X)\,B}}
 \ \le\ \frac q{\varphi(q)^2}\frac X B .                               \tag{4}
$$
局部系数可来自原来的素数和，也可来自第一条腿的 Vaughan Type II 项，其在 $\rho$ 的留数相同。锐截点可取 $\lfloor y\rfloor+1/2$，这给出同一个算术前缀并避开端点半权。定义 $Z_{\ge k}$ 时，对这六个双零点展开的乘积施加匹配条件，并沿用原来的复共轭、截取权和 $D_W$。驻相版本先将每条腿限制到固定带 $1+|\gamma|\asymp Z$。



## 固定标签与非驻相尾部

<small>原稿第 3 页</small>

固定一个特征。每个单位高度区间内按重数计的非平凡零点数为 $O(\log(2q(2+|t|)))$，其中 $t$ 为区间左端点。可由原始特征的零点计数公式作差得到。主特征由 $\zeta$ 的相应公式处理，非本原特征删去的有限欧拉因子在临界线上没有零点。[2]

在 $I_B$ 上，当 $|\gamma|\le C_1 Z$ 时有 $|V_\beta(\gamma)|\ll Z^{-1/2}$。若 $Z$ 有界用平凡界。若 $Z$ 大且 $|\gamma|\asymp Z$，用相位 $2\pi S\beta x+\gamma\log x$ 的二阶导数 $-\gamma/x^2$。若 $|\gamma|/Z$ 足够小，一阶导数单调且模长 $\gg Z$。高尺度的完整标准区间取在 $|\beta|\asymp B/X$ 上。这些导数检验对一致有界变差的振幅成立。取 $C_1$ 足够大，$|\gamma|>C_1Z$ 时，一阶导数的模长 $\gg |\gamma|$，所以 $|V_\beta(\gamma)|\ll1/|\gamma|$。

对 $\gamma$ 按不同纵坐标求和。由上述导数界与零点计数，对任一特征有
$$
 \sup_{\gamma,\,\beta\in I_B}|c_{\chi,\gamma}(\beta)|\ll L,\qquad
 \sum_{\gamma}\sup_{\beta\in I_B}|c_{\chi,\gamma}(\beta)|\ll ZL^2 .    \tag{5}
$$
事实上，$|\gamma|\le C_1 Z$ 的重数总和 $\ll ZL$。在 $C_1 Z<|\gamma|\le X^2$ 的每个二进高度段，未归一化的 $\sum m_\gamma/|\gamma|$ 至多为 $O(L)$，总计 $O(L^2)$。这也证明了后文所用的更细的尾项界
$$
 \sum_{|\gamma|>C_1 Z}\sup_{\beta\in I_B}|c_{\chi,\gamma}(\beta)|
 \ll \sqrt Z\,L^2.                                                     \tag{6}
$$
对原锐截点的驻相带，这些均为有限和。对平滑截点，令 $\delta=X^{4/5}$，以固定光滑概率密度平均 $P_{y-\delta v}$，$0<v<1$。缩放后的 $j$ 阶导数为 $O_j((1+S/\delta)^j)$。在 $\log x$ 上分部积分 $N$ 次给
$$
 |V_\beta(\gamma)|\ll_N
 (1+S|\beta|+S/\delta)^N(1+|\gamma|)^{-N}.
$$
在 $|\gamma|>X^2$ 上，式 (2) 使分子基数 $\ll\sqrt X L+X^{1/5}$。再用单位区间零点数，取 $N$ 充分大，整个尾部可小于任意给定的 $X^{-A}$。这使无限留数和可绝对重排，常数对移动截点 $y$ 一致。



## 对偏移做均方，保留零点的相位

<small>原稿第 4 页</small>

对于固定的 $\chi$，取任意与 $\beta$ 无关的允许纵坐标集合 $E_\chi$。这允许去掉已固定的标签。令
$$
 d_\chi(\beta)=\sum_{\gamma\in E_\chi}c_{\chi,\gamma}(\beta),\qquad
 \mathbb E_B f=|I_B|^{-1}\int_{I_B}f(\beta)\,d\beta .
$$
**偏移均方引理。** 在上述两种截点约定下，对任何这样的集合都有
$$
             \mathbb E_B |d_\chi(\beta)|^2\ll Z L^4.                   \tag{7}
$$
若 $SB/X\le 1$，用 (5)。在 $SB/X\ge1$ 时，先取 $E_\chi^0=E_\chi\cap\{|\gamma|\le C_1Z\}$，把含这些零点的未归一化和写成
$$
 \int g(x)x^{-1/2}A_\chi(\log x)e(S\beta x)\,dx,\qquad
 A_\chi(u)=\sum_{\gamma\in E_\chi^0}m_\gamma S^{i\gamma}e^{i\gamma u}.
$$
取固定非负光滑函数 $\psi$，在 $g$ 的对数支撑上大于等于一。其傅里叶变换的模为 $O((1+|v|)^{-2})$。对每个 $\gamma$ 按单位区间求和可得
$$
 \sum_{\gamma'\in E_\chi^0}
       \frac{m_{\gamma'}}{(1+|\gamma-\gamma'|)^2}\ll L,\qquad
 \int\psi(u)|A_\chi(u)|^2\,du\ll L\sum_{\gamma\in E_\chi^0}m_\gamma
       \ll ZL^2 .                                                       \tag{8}
$$
式 (8) 先展开平方，再对核的每一行求和，故允许重零点和任意密接的纵坐标。将 $\beta$ 积分延拓至实轴，在 $x$ 上用 Fourier–Plancherel，未归一化的平方积分至多 $CZL^2/S$。回到 (3) 后乘 $Z$，再除以 $|I_B|\asymp B/X\asymp Z/S$，驻相及低高度部分的均方至多 $CZL^2$。式 (6) 给其余高度的均方 $O(ZL^4)$。两部分相加得到 (7)。

这里的因子 $Z^{1/2}$ 来自先把零点相位求和，再在同一个偏移区间积分。将区间再切细、对每块分别用点态上界，无法保留式 (8) 的增益。



## 一个分子上的两条自由特征和

<small>原稿第 5 页</small>

记 $\mathbb E_q$ 为在 $U_q$ 上的均匀平均。把一个自由标签的允许零点先合成为 $d_\chi(\beta)$，再令
$$
 F(a,\beta)=\sum_{\chi\bmod q} \chi(a)d_\chi(\beta).
$$
每个偏移的字符正交给出精确等式 [3]
$$
 \mathbb E_q|F(a,\beta)|^2=\sum_{\chi\bmod q}|d_\chi(\beta)|^2 .
$$
将它与式 (7) 合并。对同一分子、同一偏移上的两个自由标签，允许它们有不同的物理尺度及不同的排除集合。Cauchy–Schwarz 给
$$
\begin{aligned}
 \mathbb E_q\mathbb E_B|F|^2&\ll \varphi(q)ZL^4,\\
 \mathbb E_q\mathbb E_B|F_1F_2|
 &\le (\mathbb E_q\mathbb E_B|F_1|^2)^{1/2}
       (\mathbb E_q\mathbb E_B|F_2|^2)^{1/2}.
\end{aligned}                                                         \tag{9}
$$
因 $Z\ll B$，每个自由标签至多花费 $O(\sqrt{qB}\,L^2)$，由 (2) 又至多为 $O(\sqrt H\,L^2)$。一条自由标签时由 (9) 对常函数一使用同一不等式。复共轭保持模长。此处的特征包括非本原特征。

**比较三次求和的次序。** 在 (3) 的归一化下，逐个对特征和纵坐标取模给 $O(\varphi(q)ZL^2)$。先在单位分子上作均方，给 $O(\sqrt{\varphi(q)}ZL^2)$。再保留偏移积分，给 $O(\sqrt{\varphi(q)Z}\,L^2)$。最后一式在 $q$ 小而 $B$ 大的块上仍有实质增益。

式 (9) 对整个标准区间和所有单位分子成立。应用时要先在原来的几何截取权下把自由标签合成为 $F$，随后才对所得乘积取模、放宽分子和积分区域。若先对每个零点元组取模，再对元组求和，正交所需的交叉项已经被删去。



## 匹配有重数时如何固定标签

<small>原稿第 6 页</small>

在模数 $q$ 上，令 $s_q^+,s_q^-$ 分别为正、负两侧使用该模数的积分位置数。每个位置有两个标签。令
$$
 h_q=\min(s_q^+,s_q^-),\quad h=\sum_q h_q,\quad
 m=\sum_{\lambda}\min(n_+(\lambda),n_-(\lambda)).
$$
$n_\pm(\lambda)$ 是该标签在相应一侧的出现次数。于是 $m\le2h$。当 $h=3$ 时两侧模数多重集相同。当 $h=2$ 时有两个共同模数位置，余下正、负两侧各一个，其模数不同，但可能等于共同模数之一。

在每个模数上，将位置较少的一侧全部定为参考位置。两侧相等时选正侧。所得参考位置集记作 $\mathcal A$，其大小为 $h$。先固定其中所有标签值。对每个非参考标签，分成等于某个**不同的**参考标签值、或在参考标签表以外这几种选择。每个有序元组恰在一种情形中，所需情形个数有绝对常数上界。

给定这些选择以后，每个已知值有多少次能匹配完全确定。所有表外标签都出现在本模数的同一侧，可彼此相等。它们可以独立求和，不会产生新的跨侧匹配。若 $m\ge k$，非参考位置的 $12-2h$ 个标签中，至少 $k$ 个已经取已知值。因此表外标签数 $f$ 满足
$$
                           f\le 12-2h-k.                               \tag{10}
$$
即使一个零点重数大于一，标签出现次数与单个留数的解析重数依然分别按本页和式 (3) 计算。

对每个已知值的再次出现用 (5) 的一致界。对每个参考标签的初始选择用 $\sum_{\chi,\gamma}\sup_{\beta}|c_{\chi,\gamma}(\beta)|\ll\varphi(q)B L^2$。这样可在参考位置除去分子及偏移的依赖。自由标签仍按式 (9) 合成。若积分权依赖全部六个分子和偏移，此时才取模舍去该权。此操作仍保留 $|D_W(\Delta)|$。



## 最小公倍数与偏移区间的平均

<small>原稿第 7 页</small>

固定非参考位置的分子、偏移和全部参考标签值，放宽参考分子的互素约束。令
$$
 K=\operatorname{lcm}(q_i:i\in\mathcal A),\qquad
 B_A=\max_{i\in\mathcal A} B_i.
$$
参考位置的带符号分子和把 $\prod_{i\in\mathcal A}\mathbb Z/q_i\mathbb Z$ 满射至 $K^{-1}\mathbb Z/\mathbb Z$。这是因为 $K/q_i$ 的最大公因数为一，而正负号不改变生成子群。各纤维等大。对任意其余变量给定的平移 $v$，平均后的核为
$$
 G_K(v)=K^{-1}\sum_{j=0}^{K-1}|D_W(v+j/K)|.
$$
由 Poisson 求和和 $W$ 的光滑紧支撑，$\|D_W\|_{L^1(\mathbb T)}\ll_W1$。$G_K$ 的周期为 $1/K$，一周期的积分至多 $C_W/K$。长 $\ell$ 的区间由至多 $\lfloor K\ell\rfloor+1$ 个周期长的区间覆盖。对宽度最大的参考偏移使用这个界，其余参考偏移只用区间长度。因此，归一化平均 $|D_W|$ 的代价至多
$$
 C_W\left(1+\frac X{KB_A}\right).                                     \tag{11}
$$
该上界对所有非参考变量一致，随后各非参考位置可在自己的 $(a,\beta)$ 上应用 (9)。

每个位置的长度 $O(B_i/X)$ 与 (4) 中的 $X/B_i$ 相消。将分子求和写成平均，分子个数与 Gauss 因子合计至多 $(q_i/\varphi(q_i))^2$。这些比率和有限个对数因子均可吸入 $X^\varepsilon$。固定所有模数、物理尺度、偏移尺度以及匹配情形后，积分贡献的模至多
$$
 \boxed{\quad
 \ll_\varepsilon X^\varepsilon\!
   \left(1+\frac X{K B_A}\right)
   \prod_{i\in\mathcal A}(q_iB_i)^2
   \prod_{\ell\ {\rm free}}\sqrt{q_\ell B_\ell}\; .\quad}             \tag{12}
$$
后续用 $\prod(q_iB_i)^2\le H^{2h}$，各自由因子至多 $\sqrt H$。全部二进块的个数为固定次对数。式 (12) 也适用于根据事先指定的跨侧相等关系选出的参考位置，只须每条相等关系都有一个端点在参考位置，并对不受约束的标签独立求和。



## 四个匹配与三个匹配的全部模数

<small>原稿第 8 页</small>

对 $m\ge3$，式 (10) 只允许 $h=2,3$。模数组数取决于 $h$，所以要连同式 (11) 一起计算。对固定的 $r\ge1$，有
$$
 \sum_{p_1,\ldots,p_r\le D}\frac1{[p_1,\ldots,p_r]}
 \le\sum_{K\le D^r}\frac{\tau(K)^r}{K}\ll_\varepsilon X^\varepsilon.  \tag{13}
$$
方括号表示最小公倍数，$p_i$ 是任意正整数模数。按 $K$ 分组时每个 $p_i$ 都整除 $K$。末式用固定次除数界并相应缩小 $\varepsilon$。

**两侧模数多重集相同。** 此时 $h=3$，固定正侧三个模数后，负侧至多有 $3!$ 种排列。参考模数允许重复。式 (10) 给 $f\le6-k$。在 (12) 放宽 $B_A\ge1$，对三个模数使用 (13)，得到
$$
 |Z^{\rm bal}_{\ge k}|
 \ll_\varepsilon X^\varepsilon H^{6+(6-k)/2}(D^3+X)
 \ll_\varepsilon X^{6-k/4+\varepsilon},\quad 3\le k\le6 .             \tag{14}
$$
对数因子在末式中已吸收。$k=6,5,4,3$ 分别给出式 (1) 的四个指数。

**两侧模数多重集不同。** 此时 $h=2$。把两个参考模数记作 $p_1,p_2$，另外各多出来的一个正、负模数记作 $u,v$。允许 $p_1=p_2$ 以及 $u$ 或 $v$ 等于参考模数。位置排列只有有界多种。放宽对 $u,v$ 的限制，先用 (13) 对 $\operatorname{lcm}(p_1,p_2)^{-1}$ 求和，得
$$
 |Z^{\rm unbal}_{\ge k}|
 \ll_\varepsilon X^\varepsilon H^{4+(8-k)/2}D^2(D^2+X)
 \ll_\varepsilon X^{6-k/4+\varepsilon},\quad k=3,4 .                  \tag{15}
$$
在 $k=5,6$ 时，不同模数多重集不允许这么多匹配。合并 (14)、(15) 证明式 (1)。取 $\varepsilon=1/8$，四匹配的指数为 $41/8$，三匹配为 $43/8$，均小于目标指数 $44/8$。因此跨过目标时无需把一个 $X^\varepsilon$ 直接替换成某个固定次的对数。



## 两侧模数相同时再保留一个匹配

<small>原稿第 9 页</small>

对 $k=1,2$，用 $Z^{\rm bal}_{\ge k}$ 表示两侧模数多重集相同且至少有 $k$ 对匹配的带符号和。当三个正侧模数中至多有两个不同值时，继续用三个参考位置。式 (10) 给 $f\le5$。普通模数组数至多 $O(D^2)$，含 $1/K$ 的和仍由 (13) 控制，因而这部分为
$$
        O_\varepsilon\big(X^\varepsilon H^{6+5/2}(D^2+X)\big)
        =O_\varepsilon(X^{21/4+\varepsilon}).
$$
现在三个模数各不相同，每个模数恰有一个正位置和一个负位置。把“至少 $k$ 对匹配”写成有限个事件的并，每个事件指定 $k$ 对不重复位置上的相等标签。对这个并作容斥，每一交集只强制若干跨侧等式。由于标签位置总数固定，全部容斥系数绝对值之和有绝对常数上界。这样可以在没有指定等式的模数上，把两侧标签都当作自由标签。

若某个交集中，有 $r$ 个不同模数出现了指定等式，则 $1\le r\le3$。仅取这些模数的正位置作参考。固定它们的标签，等式不相容时贡献为零。相容时，负侧至少 $r$ 枚标签的值已经确定。于是剩余自由标签至多 $12-3r$。由 (12) 得到该交集的上界
$$
       \ll_\varepsilon X^\varepsilon H^{6+r/2}
          \big(D^3+XD^{3-r}\big).                                    \tag{16}
$$
其中 $D^{3-r}$ 来自没有指定等式的模数，另 $r$ 个模数的 $1/K$ 和已用 (13) 处理。对 $r=1,2,3$，式 (16) 的指数依次为 $21/4,5,21/4$，各带任意小的 $\varepsilon$。因此
$$
 \boxed{\ \sup_y|Z^{\rm bal}_{\ge k}(y)|
           \ll_\varepsilon X^{21/4+\varepsilon}\quad(k=1,2).\ }        \tag{17}
$$
此证明对两个 $k$ 分别应用容斥。带符号的子和不具有单调性，从一个较大集合的上界直接推向子集会遗漏这一点。



## 尚未跨过目标的一个具体配置

<small>原稿第 10 页</small>

设两侧模数分别为 $\{p,u_1,u_2\}$、$\{p,v_1,v_2\}$，五个数各不相同。模 $p$ 的两个正标签分别匹配两个负标签。其他四个位置有八个自由标签。取模 $p$ 的正位置作参考，式 (12) 在固定模数组上给
$$
 \ll_\varepsilon X^\varepsilon
  (pB_p)^2
  \prod_{\ell\ {\rm free}}\sqrt{q_\ell B_\ell}
  \left(1+\frac{X}{p B_p}\right).
$$
先对四个额外模数求和，再对 $p$ 求和。常数项至多 $X^\varepsilon H^6D^5\ll_\varepsilon X^{11/2+\varepsilon}$。周期余项由 (13) 粗估至多 $X^{1+\varepsilon}H^6D^4\ll_\varepsilon X^{6+\varepsilon}$。这只是本方法给出的上界。它指出一个尚须利用额外抵消的模数组合。零匹配部分、其余未处理的低匹配部分，以及展开中的极点与移线余项也须纳入原目标。

**Vaughan 对数权。** 写 $\mathcal L(s)=L(s,\chi)$，$M_U=\sum_{d\le U}\mu(d)\chi(d)d^{-s}$，$P_V=\sum_{r\le V}\Lambda(r)\chi(r)r^{-s}$。Type II 级数为
$$
 (-\mathcal L'/\mathcal L-P_V)(1-\mathcal L M_U).
$$
在 $\mathcal L(\rho)=0$ 处，第二因子等于一，留数恰为 $-m_\rho$。因此在这一步计入 $\log$ 权后仍须承担完整的零点留数。(7) 至 (9) 给出本次节省所依赖的振荡。前稿已控制锐截点在物理长度 $X^{4/5}$ 上平滑造成的**完整带窗六阶范数**误差。这允许在判断完整目标时使用平滑版本。对单独截取的谱项，本文对原锐截点给出驻相带结果，对平滑截点给出全部高度结果。[1]

### 文献与核验

[1] [前稿《用 Mellin 变换分离哥德巴赫六阶矩的 Type I 项》](08-mellin.md)，式 (9)、(10)、(14)、(15)。[原六重积分与微观边的定义](07-arcs.md)，式 (10) 至 (15)。

[2] Bennett、Martin、O’Bryant、Rechnitzer，[Counting Zeros of Dirichlet $L$-Functions](https://arxiv.org/abs/2005.02989)。[Davenport，Multiplicative Number Theory](https://link.springer.com/book/9780387950976)，第 16 章。

[3] A. J. Hildebrand，[Introduction to Analytic Number Theory](https://eclass.uoa.gr/modules/document/file.php/MATH717/04.%20%CE%92%CE%BF%CE%B7%CE%B8%CE%AE%CE%BC%CE%B1%CF%84%CE%B1/Analytic-number-theory-Hildebrand.pdf)，定理 6.7。

配套文件使用 Lean 4.19.0 和同版本 mathlib。23 个引理均经内核检查，包含固定模数的 Parseval 等式、在连续偏移上积分后的等式、共用 $(a,\beta)$ 时的 Cauchy–Schwarz、零点核的有限行和推论、多重集计数、满射纤维等势和指数运算。实轴上的 Fourier–Plancherel、振荡积分、零点计数及由它们推出的式 (1) 由正文证明。
