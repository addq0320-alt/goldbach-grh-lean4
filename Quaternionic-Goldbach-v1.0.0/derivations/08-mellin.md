# 用 Mellin 变换分离哥德巴赫六阶矩的 Type I 项

<small>原稿第 1 页</small>

设 $X$ 充分大，$L=\log(2X)$，$e(t)=e^{2\pi it}$。全篇假设所有 Dirichlet $L$ 函数的 GRH。沿用前稿的等宽主弧，取 $Q=\lfloor X^{3/10}\rfloor$，各既约分数 $a/q$、$q\le Q$ 的半宽为 $L^4/X$。小弧记为 $\mathfrak m$。对函数 $F$ 记
$$
 C[F](n)=\int_{\mathfrak m}F(\alpha)P_\eta(\alpha)e(-n\alpha)\,d\alpha,\qquad
 \|c\|_{6,W}^6=\sum_{n\in2\mathbb Z} W(n/X)|c(n)|^6 .
$$
$P_\eta(\alpha)=\sum_j\Lambda(j)\eta(j/X)e(j\alpha)$。光滑权 $\eta,W$ 沿用前稿。$\eta$ 在真实平衡区间所需范围为一，$W\ge0$ 在 $[1,2]$ 为一，支撑位于固定的 $[c,C]\subset(0,\infty)$。傅里叶变换约定为负号。以下估计对 $0\le y\le 2X$ 一致。

**Type I 定理。** 若 $1\le D\le Q$，$|a_d|\le A$，令
$$
 T_y(\alpha)=\sum_{d\le D}a_d\sum_{1\le m\le y/d}e(dm\alpha).
$$
对任何固定 $\varepsilon>0$ 有
$$
 \boxed{\displaystyle
 \sup_y\|C[T_y]\|_{6,W}^{6}
 \ll_{\varepsilon,\eta,W}
 A^{6}\big(X^4D^5L^{18}+X^{26/5+\varepsilon}\big).}                 \tag{1}
$$
本式允许原来的锐截点。取 $D=\lfloor X^{3/10}/L^3\rfloor$，把一个素数因子按 Vaughan 恒等式展开。包括对数权在内的两个 Type I 项合计为 $O(X^{11/2}L^9)$ 的六阶矩。可在完整带窗矩中移去它们。

**Type II 的部分上界。** 前稿的目标 $\sup_y\operatorname{Re}\mathcal J_y\ll X^{11/2}L^{12}$，在这个尺度等价于第 5 页式 (9)。对其中位于驻相高度的双零点项，正负两侧各有六个标签 $(q,\chi,\gamma)$。六个均可一一匹配时，全部模数合计为 $O_\varepsilon(X^{9/2+\varepsilon})$。至少五个匹配时为 $O_\varepsilon(X^{5+\varepsilon})$。第 12 页还证明，在指定的对称小弧子区，只要总特征非主，全部相应分子的带符号和就严格为零。该抵消允许任意零点高度。式 (9) 的完整上界仍待证明。



## 同一条 Perron 积分线控制移动截点

<small>原稿第 2 页</small>

对 $(r,d)=1$ 写
$$
 E_d(t,r)=\sum_{\substack{j\le t\\j\equiv r\ (d)}}\Lambda(j)-t/\varphi(d).
$$
在 $d\le X$ 时成立
$$
 \left(\sum_{r\bmod d}^{*}
            \sup_{0\le t\le CX}|E_d(t,r)|^2\right)^{1/2}
      \ll_C \sqrt X L^3 .                                             \tag{2}
$$
上确界放在每个剩余类内部，因而各类的截点可以彼此不同。

**证明。** 写 $\sigma=\tfrac12+1/L$，$T=X^4$，$F_\chi=-L'/L(\cdot,\chi)$。先将 $t$ 换成 $\lfloor t\rfloor+1/2$，原计数不变，主项改变 $O(1)$。在 $\Re s=1+1/L$ 截断 Perron 并左移至 $\sigma$，得到
$$
 \sum_{j\le t}\Lambda(j)\chi(j)-{\bf1}_{\chi=\chi_0}t
   =\frac1{2\pi}\int_{-T}^{T} F_\chi(\sigma+iv)
       \frac{t^{\sigma+iv}}{\sigma+iv}\,dv+O_C(1).                    \tag{3}
$$
对每个半整数 $t$ 一致。截断误差由
$\sum_j\Lambda(j)(t/j)^{1+1/L}\min(1,(T|\log(t/j)|)^{-1})$ 控制。在 $t/2<j<2t$ 用 $|t-j|\ge1/2$ 并按距离求和，其余部分用绝对收敛，得到 $O_C(1)$。移线只越过主特征在 $1$ 的极点。GRH 与对数导数的局部零点展开给 $|F_\chi(\sigma+iv)|\ll_C L^2$，因为每个单位高度区间有 $O(\log(2d(T+2)))$ 个零点，每个分母至少 $1/L$。两条水平边同理，积分为 $O_C(XL^2/T)$。非本原特征删去的欧拉因子贡献 $O(\log(2d))$。[2]

将 (3) 乘 $\bar\chi(r)/\varphi(d)$ 后先加合，再对 $t$ 取上确界。$t^\sigma\ll_C\sqrt X$，$|t^{iv}|=1$。对 $r$ 用积分型 Minkowski 不等式。每个高度的剩余类均方根恰为
$$
 \left(\frac1{\varphi(d)}
      \sum_{\chi\bmod d}|F_\chi(\sigma+iv)|^2\right)^{1/2}\ll L^2 .
$$
最后 $\int_{-T}^T|\sigma+iv|^{-1}dv\ll L$，每行 $O_C(1)$ 的合计成本 $O_C(\sqrt d)$。这给出 (2)。



## 完整傅里叶系数与主项

<small>原稿第 3 页</small>

记 $I_n(y)=\int_0^y\eta((n-t)/X)dt$，令
$$
 M_y(n)=I_n(y)\sum_{\substack{d\le D\\(d,n)=1}}\frac{a_d}{\varphi(d)}.
$$
记 $R_y^I(n)$ 为 $T_yP_\eta$ 在**整圆**上的第 $n$ 个系数。卷积给出
$$
 R_y^I(n)=\sum_{d\le D}a_d
 \sum_{\substack{n-y\le j<n\\j\equiv n\ (d)}}\Lambda(j)\eta(j/X).
$$
这里的截点 $n,n-y$ 随表示整数移动，端点可用左极限处理。固定 $d$，当 $(n,d)=1$ 时，局部误差由 $\sup_t|E_d(t,n\bmod d)|$ 乘一个只依赖 $\eta$ 的常数控制，这是对有界变差权分部求和。由于 $\eta$ 的支撑在正半轴，负截点以零处理。当 $(n,d)>1$ 时，可能的 $j$ 都是 $p\mid d$ 的素数幂，其 $\Lambda$ 总和 $\ll L^2$。该情形的主项为零。

因此在 $cX\le n\le CX$ 上，完整误差 $F_y(n)=R_y^I(n)-M_y(n)$ 满足
$$
 \|F_y\|_\infty\ll A\sqrt X\,D L^3,\qquad
 \left(\sum_n|F_y(n)|^2\right)^{1/2}\ll A X\sqrt D\,L^3.            \tag{4}
$$
首式对每个 $d$ 用 (2)。次式中，每类出现 $O_C(X/d)$ 次，所以一个 $d$ 对 $\ell^2$ 范数至多贡献 $O_\eta(XL^3/\sqrt d+\sqrt X L^2)$。用 $d\le X$，对 $d$ 求和即得。乘上有界的 $W$ 并限制在偶数只改常数。用 $\sup|F_y|^4$ 乘平方和即得 $O(A^6X^4D^5L^{18})$。

**同一个主项的有限分母公式。** $c_q(n)=\sum_{a\bmod q}^{*}e(an/q)$ 为 Ramanujan 和。对每个 $d$，
$$
 \sum_{q\mid d}\frac{\mu(q)c_q(n)}{\varphi(q)}
    =\frac d{\varphi(d)}{\bf1}_{(n,d)=1}.                             \tag{5}
$$
左边分解为 $\prod_{p\mid d}(1-c_p(n)/(p-1))$。若 $p\mid n$，对应因子为零。否则等于 $p/(p-1)$。这是保留不同分母符号的精确抵消，在 $d$ 和 $n$ 有公因子时尤其关键。



## 主弧误差与 Type I 小弧界

<small>原稿第 4 页</small>

在 $\alpha=a/q+\beta$，$q\le Q$，$|\beta|\le Z/X$，$Z=L^4$，写
$$
 T_y=A_qV_y+G,\qquad P_\eta=\lambda_qV_\eta+E,\qquad
 A_q=\sum_{\substack{d\le D\\q\mid d}}\frac{a_d}{d},\quad
 \lambda_q=\frac{\mu(q)}{\varphi(q)}.
$$
$V_y=\int_0^y e(t\beta)dt$，$V_\eta=\int\eta(t/X)e(t\beta)dt$。有 $|A_q|\ll AL/q$（$q>D$ 时为零）以及
$$
 |G|\ll A(D+q)L(1+X|\beta|),\qquad
 \sum_{a\bmod q}^{*}|E|^2\ll qX L^4(1+X|\beta|)^2.                  \tag{6}
$$
前式对 $q\mid d$ 用离散和与积分之差 $O(1+X|\beta|)$，对 $q\nmid d$ 用分部求和与几何级数。每个完整的 $q$ 长的 $d$ 区间，非零剩余类的 $\|ad/q\|^{-1}$ 总和为 $O(q\log(2q))$。后式是前稿式 (4) 的特征正交估计。[1]

模型 $A_q\lambda_q V_yV_\eta$ 的系数为 $M_y(n)+O_B(AX^{-B})$，任意固定 $B>0$。因 $\eta$ 的傅里叶衰减为 $O(e^{-c\sqrt{|v|}})$，可延拓 $\beta$ 积分得到 $I_n(y)$。再按 $d$ 合并分母，再用 (5)，所有 $q\mid d$ 均已计入。

以下上界中 $X^\varepsilon$ 吸收对数。对 $A_qV_yE$，在每个 $\beta$ 先用 (6) 对分子求和，并用 $|V_y|\ll X/(1+X|\beta|)$，得到
$$
 \|\widehat{\mathbf1_{\mathfrak M} A_qV_yE}\|_\infty
     \ll_\varepsilon A X^{1/2+\varepsilon}D,\qquad
 \|\mathbf1_{\mathfrak M} A_qV_yE\|_2^2\ll_\varepsilon A^2X^{2+\varepsilon}.
$$
平方界对不交弧积分，分母和至多损失 $\sum_{q\le D}1/q$。故六次和 $\ll_\varepsilon A^6X^{4+\varepsilon}D^4$。对 $\lambda_qV_\eta G$ 的每个系数，绝对积分上界为 $O_\varepsilon(AX^\varepsilon Q(D+Q))$，用 $\int |V_\eta|(1+X|\beta|)d\beta\ll1$。对 $GE$ 由 (6) 得 $O_\varepsilon(AX^{-1/2+\varepsilon}Q^2(D+Q))$。将后两项各取六次方后对 $O(X)$ 个整数求和。代入 $D\le Q\le X^{3/10}$，三个六次和依次为
$$
 \ll_\varepsilon A^6 X^{26/5+\varepsilon},\qquad
 \ll_\varepsilon A^6 X^{23/5+\varepsilon},\qquad
 \ll_\varepsilon A^6 X^{17/5+\varepsilon}.
$$
整圆与主弧都扣去同一 $M_y$ 后相减，由 (4) 得 (1)。



## 把原单侧目标化为一个 Type II 矩

<small>原稿第 5 页</small>

取 $D=\lfloor X^{3/10}/L^3\rfloor$，可取 $U=V=\lfloor\sqrt D\rfloor$。在 Dirichlet 卷积中用 $\mu*{\bf1}=\delta$，$\Lambda*{\bf1}=\log$，有 Vaughan 恒等式 [3]
$$
 \Lambda=\mu_{\le U}*\log
 -(\mu_{\le U}*\Lambda_{\le V})*{\bf1}
 +\Lambda_{\le V}+\Lambda_{>V}*(\mu_{>U}*{\bf1}).                    \tag{7}
$$
第二项的外系数支撑在 $d\le UV$，模长 $\le\sum_{b\mid d}\Lambda(b)=\log d$。第一项用 $\log m=\log(dm)-\log d$。第一部分对 $dm$ 分部求和，带窗 $\ell^6$ 范数至多损失 $2L$，第二部分的外系数模长至多 $L$。由 (1)，两个 Type I 项合计的六阶矩为 $O(X^{11/2}L^9)$，因为 $D^5L^{24}\le X^{3/2}L^9$。$X^{26/5+\varepsilon}$ 可选固定小 $\varepsilon$ 吸收其余对数。对小支撑的 $\Lambda_{\le V}$ 项，Cauchy、Parseval 与前稿的小弧 $\sup|P_\eta|\ll X^{3/4}L^{3/2}$ 给出六次和 $\ll X^{7/2}V^3L^8$。

令 $b_U(s)=\sum_{d\mid s,\,d>U}\mu(d)$，余项对应
$$
 T_y^{II}(\alpha)=
 \sum_{\substack{r>V,\ s>U\\rs\le y}}
       \Lambda(r)b_U(s)e(rs\alpha).                                    \tag{8}
$$
写 $P_y=\sum_{m\le y}\Lambda(m)e(m\alpha)$。前稿式 (10)、(13)、(14) 给
$|\|C[P_y]\|_{6,W}^6-\operatorname{Re}\mathcal J_y|\ll X^{11/2}L^{12}$。[1]
在完整带窗矩上应用 (7) 及 $\ell^6$ 三角不等式，得到
$$
 \big|\|C[P_y]\|_{6,W}-\|C[T_y^{II}]\|_{6,W}\big|
     \ll X^{11/12}L^{3/2}.
$$
于是 $\sup_y\operatorname{Re}\mathcal J_y\ll X^{11/2}L^{12}$ 等价于
$$
 \boxed{\displaystyle
 \sup_{0\le y\le2X}
 \sum_{n\in2\mathbb Z}W(n/X)
       \left|\int_{\mathfrak m}T_y^{II}(\alpha)P_\eta(\alpha)e(-n\alpha)d\alpha\right|^6
 \ll X^{11/2}L^{12}.}                                                  \tag{9}
$$
这里对 Type I 的控制包括退化参数在其总和中的作用。若只看单个倒数和，写单位类权为 $b=\bar b+(b-\bar b)$，其中 $\bar b$ 是单位类平均。则 $\sum_r^* b(r)e(t\bar r/q)=\bar b c_q(t)+\sum_r^*(b(r)-\bar b)e(t\bar r/q)$。在 $t=(n-j)h\equiv0\pmod q$ 时残项恰为零，原和为 $\varphi(q)\bar b$。这个局部等式同时说明了为何不能孤立删除零频。



## 锐截点可以在多宽的区间上平滑

<small>原稿第 6 页</small>

置 $H=X^{4/5}$。对 $0\le y_0\le y_1\le2X$、$y_1-y_0\le H$，有
$$
 \left\|C[P_{y_1}-P_{y_0}]\right\|_{6,W}^6\ll X^{11/2}L^{12}.         \tag{10}
$$
这给出已达标的一整段截点 $0\le y\le H$，也控制了任意位置上宽 $H$ 的截点变化。

**证明。** 记 $P=P_{y_1}-P_{y_0}$。整圆系数大小 $\ll (H+1)L^2$，直接用区间内项数与两份 $\Lambda$ 即得。偶数 $n\asymp X$ 的主项为 $S_n(I_n(y_1)-I_n(y_0))$，大小亦 $\ll (H+1)L^2$，其中通常的二元奇异级数满足 $S_n\ll L$。为估计这个欧拉积，依次列出 $n$ 的奇素因子 $p_i$，用 $p_i-2\ge i$，便有 $\prod_i(1+1/(p_i-2))\le 1+\omega(n)$。

取 $M=C_\eta(H+1)L^2$，使整圆系数与主项的差至多 $M$。若 $E(n)$ 是这段的主弧误差，由前稿截点估计 (6) 两次相减，$\|E\|_{6,W}^6\ll_\varepsilon X^{26/5+\varepsilon}$。该标量估计对 $n$ 只用了 $n\asymp X$ 和 $O(X)$ 个整数，故覆盖整个 $W$ 支撑。现在 $|C[P](n)|\le M+|E(n)|$。

GRH 下区间内的 $\Lambda$ 总和 $\ll H+\sqrt X L^2\ll H$，故 $\int|P|^2\ll HL$。配合小弧光滑素数和的一致界，得到
$$
 \sum_n W(n/X)|C[P](n)|^2\ll X^{3/2}HL^4.
$$
当 $|C[P](n)|\le2M$ 时用 $(2M)^4|C[P](n)|^2$ 控制六次幂。其余情形用 $2^6|E(n)|^6$。因此总和
$\ll_\varepsilon X^{3/2}H^5L^{12}+X^{26/5+\varepsilon}$，给出 (10)。

可取固定的光滑概率密度 $\rho\in C_c^\infty((0,1))$，以 $\int_0^1\rho(v)P_{y-Hv}\,dv$ 代替 $P_y$（负截点取零），误差由 Minkowski 和 (10) 控制。对 (8) 的截点作同一平滑，使用 (7) 及第 5 页的一致界，仍得到与 (9) 等价的判据。平滑过渡宽度是 $X^{4/5}$。若改用 $u=m/X$，第 $k$ 阶导数可能损失 $O_k(X^{k/5})$。用驻相法时须计入这项依赖。



## 联立两个 Mellin 频率与一个加法频率

<small>原稿第 7 页</small>

以下是具有固定光滑权的局部积分。取 $f,g\in C_c^\infty((0,\infty))$，$w$ 固定光滑，支撑在 $1\le|\lambda|\le2$ 的一个符号区间。令 $B\ge1$，$z=n/X\in[c,C]$。两个临界线 Mellin 核与一段加法频率的积分为
$$
 \begin{aligned}
 K_B(z;t,s)&=B\iiint
 \frac{w(\lambda)f(u)g(v)}{\sqrt{uv}}\,
     e^{i\Phi}\,du\,dv\,d\lambda,\\
 \Phi&=t\log u+s\log v+2\pi B\lambda(u+v-z).
 \end{aligned}                                                         \tag{11}
$$
对 $\lambda$ 先作傅里叶变换，恰得核 $B\widehat w(B(z-u-v))$。同时保留三个变量时，驻点方程给
$$
 u+v=z,\quad t=-2\pi B\lambda u,\quad s=-2\pi B\lambda v .
$$
因此驻相要求 $ts>0$、$|s|,|t|\asymp B$，并要求下列坐标落入各自的支撑
$$
 u_*=\frac{zt}{t+s},\qquad v_*=\frac{zs}{t+s},\qquad
 \lambda_*=-\frac{t+s}{2\pi Bz}.                                      \tag{12}
$$
若支撑上一致有 $|\nabla\Phi|\ge c_1(B+|t|+|s|)$，沿 $\nabla\Phi$ 反复分部积分，得到 $K_B\ll_{N,c_1}B(1+B+|t|+|s|)^{-N}$。例如异号且 $|s|,|t|\asymp B$ 时，这个条件成立。在 $B\ge X^\delta$ 的非驻相块上可得到任意固定 $X$ 负幂。在对数尺度保留 $B$ 的衰减。

驻点处 Hessian 的行列式为 $(2\pi B)^2(t/u_*^2+s/v_*^2)$，绝对值 $\asymp B^3$。若驻点位于支撑内部的固定紧子区，三维驻相法给主项 $B^{-1/2}a(z,t/B,s/B)e^{i\Phi_*}$，余项 $O(B^{-3/2})$。$a$ 光滑，包含 Hessian 的符号因子。任意固定阶展开也成立。[4]
$$
 \Phi_*=(t+s)\log z+
 t\log\left|\frac t{t+s}\right|+
 s\log\left|\frac s{t+s}\right| .                                      \tag{13}
$$
这一局部结果针对固定光滑权。带锐弧边界或过渡权时，须先分解并核算边界和导数。本文只在所列的光滑块上使用 (11) 至 (13)。



## Type II 仍包含哪些相位

<small>原稿第 8 页</small>

对特征 $\chi$ 记 $\mathcal L(s)=L(s,\chi)$，$M_U=\sum_{d\le U}\mu(d)\chi(d)d^{-s}$，$P_V=\sum_{r\le V}\Lambda(r)\chi(r)r^{-s}$。由 (8)，Type II 的乘法扭转 Dirichlet 级数在 $\Re s>1$ 满足
$$
 \begin{aligned}
 F_{II}(s,\chi)&=(-\mathcal L'/\mathcal L-P_V)(1-\mathcal L M_U)\\
 &= -\mathcal L'/\mathcal L+\mathcal L'M_U-P_V+P_V\mathcal L M_U .
 \end{aligned}                                                         \tag{14}
$$
等式给出亚纯延拓。在每个重数为 $m_\rho$ 的非平凡零点 $\rho$，后三项全纯。因此
$$
 \operatorname*{Res}_{s=\rho}F_{II}(s,\chi)=-m_\rho.                    \tag{15}
$$
选择 Vaughan 参数会改变 Dirichlet 多项式，但每个零点的这一留数保持为 $-m_\rho$。GRH 给出其实部，混合零点和的相位仍存在。

在六个 (13) 型主项中取前三个正号、后三个负号，置 $T=\sum_i\epsilon_i(t_i+s_i)$，$\Theta=\sum_i\epsilon_i a_i/q_i$。对紧支撑于正半轴的固定光滑权 $A(z)$（含 $W$）在正数支撑上应用 Poisson 求和得到
$$
 \sum_{n\in2\mathbb Z} A(n/X)(n/X)^{iT}e(-n\Theta)
 =\frac X2\sum_{\ell\in\mathbb Z}\int A(z)
       e^{iT\log z-2\pi iX(\Theta-\ell/2)z}\,dz.                        \tag{16}
$$
若对某个 $\ell$ 在支撑上有 $|T/z-2\pi X(\Theta-\ell/2)|\gg |T|+X|\Theta-\ell/2|$，该积分为 $O_N((1+|T|+X|\Theta-\ell/2|)^{-N})$。驻相则要求存在 $z$ 使
$$
 \Theta-\ell/2=\frac{T}{2\pi Xz}.                                      \tag{17}
$$
当 $|T|\ge1$，二阶导数为 $-T/z^2$，单个驻相积分至多 $O(|T|^{-1/2})$。当两边频率同时为零，积分恰为 $\int A$。这些界的常数依赖振幅导数。式 (17) 将分母相位与零点纵坐标联系在一起。要推出 (9)，仍需对驻相和接近驻相的模数、特征与频率总和作带符号估计。单个核的驻相衰减尚未给出这项估计。




## 驻相高度上的零点匹配

<small>原稿第 9 页</small>

实际分拆中，对 $\alpha\in\mathfrak m$ 选取可测的 Dirichlet 逼近 $a/q+\beta$，$q\le D_0=\lfloor\sqrt X/L\rfloor$，$|\beta|\le1/(qD_0)$。可在有多个选择时按固定次序选取一个。将 $1+X|\beta|$ 按 $B\ge1$ 二进分段，则
$$
 q B\ll\sqrt X L.                                                       \tag{18}
$$
将已平滑的第一个变量切在 $m\asymp M$，$1\ll M\ll X$（最低块允许 $M=1$），第二变量 $j\asymp X$。两权缩放至固定紧正区间后均有一致有界变差。对两腿与 $q$ 互素的部分，特征展开给每个零点残项系数 $\tau_a(\bar\chi)/\varphi(q)$ 乘尺度的 $\rho$ 次幂、Mellin 核及负重数。Type II 腿的留数来自 (15)，素数腿来自 $-L'/L$。可对光滑块先作有限高度移线以识别这些残项。本页只选择下述有限高度带。非单位类、其他极点和余积分未计入此界。

写 $B'=\max(1,MB/X)$。选取
$$
 1+|\gamma_1|\asymp B',\qquad 1+|\gamma_2|\asymp B,                   \tag{19}
$$
其中比较常数固定。这包含固定紧支撑所允许的驻点高度。对 $u\asymp1$，单腿相位的二阶导数是 $-\gamma/u^2$。由二阶导数检验（对有界变差振幅用分部求和），两个 Mellin 核分别为 $O((B')^{-1/2})$、$O(B^{-1/2})$。有界高度使用平凡界。又 $|\tau_a(\bar\chi)|\le\sqrt q$，因为对应加法变换的完整平方和是 $q\varphi(q)$，单位分子的模长相等。剔除留数重数后，**每个双零点项**的模长因而至多
$$
 \frac q{\varphi(q)^2}\frac{\sqrt{MX}}{\sqrt{B'B}}
    \ll \frac q{\varphi(q)^2}\frac X B .                               \tag{20}
$$

每个 $\alpha_i$ 给两个标签 $(q_i,\chi,\gamma)$。在取共轭前比较标签，把相同模数、特征和纵坐标的正、负位置一一匹配。重数另计。若至少五个匹配，正负两侧的三个模数必为同一多重集，因为对每个 $q$，该模数的标签数之差是偶数，未匹配的正、负位置各至多一个，所以差只能为零。令正侧三个模数为 $q_1,q_2,q_3$。负侧可按模数重排。这个结论也允许标签在同模数的不同双零点项间交换。



## 用最小公倍数合并分母

<small>原稿第 10 页</small>

令 $K=\operatorname{lcm}(q_1,q_2,q_3)$，$B_*=\max_{1\le i\le6}B_i$。在集体共振带内，$\Theta$ 距半整数至多 $C(B_*+L^4)/X$。放宽分子的互素限制后，分母为 $q_i$ 的差分所构成的群，通过加法同态映入 $K^{-1}\mathbb Z/\mathbb Z$，其像由 $1/q_1,1/q_2,1/q_3$ 生成，因而该映射是满射。这是一个均匀网格，每个值有 $\prod_i q_i^2/K$ 个原像。因此允许的分子六元组总数至多
$$
 \ll (q_1q_2q_3)^2\left(\frac1K+\frac{B_*+L^4}{X}\right).            \tag{21}
$$
这里和下文的三重乘积均在正侧模数上取。固定所有分子后，各积分段长 $O(B_i/X)$。对 $B_i=B_*$ 的那个坐标用 $\|D_W\|_1\ll1$，对其余坐标用区间长度，于是积分体积乘核至多为 $C(X/B_*)\prod_{i=1}^6 (B_i/X)$。这与 (20) 中六个振幅的 $X/B_i$ 完全相消，剩下 $X/B_*$ 和 Gauss 权。在共振带外，$|D_W(\Delta)|=O_N(X^{-N})$，这些有限高度带的总振幅至多为 $X$ 的固定幂。

先设六个标签全匹配。对一条特征，重数平方和 $\sum_{1+|\gamma|\ll B}m_\gamma^2\ll B L^2$（对不同纵坐标求和），由单位区间零点数 $O(L)$ 得到。三个正位置共有六个标签可选，负位置由匹配置换确定。因此固定 $q_i,B_i,M_i$ 后，计入重数的选择至多 $C\prod_{i=1}^3\varphi(q_i)^2 B_i^2L^4$。乘 (20)、(21) 与上述积分界，并用 $q/\varphi(q)\ll L$ 及 (18)，得到每个模数三元组的上界
$$
 \ll X^{4}L^{C_0}\left(\frac1K+\frac1X\right).                        \tag{22}
$$
具体地，乘积中 $\prod_{i=1}^3(q_iB_i)^2\ll X^3L^6$，而 $B_*^{-1}[K^{-1}+(B_*+L^4)/X]\ll K^{-1}+L^4/X$。剩余二进段个数是 $L$ 的固定幂。最后
$$
 \sum_{q_1,q_2,q_3\le D_0}\frac1{\operatorname{lcm}(q_1,q_2,q_3)}
 \le \sum_{K\le D_0^3}\frac{\tau(K)^3}{K}\ll_\varepsilon X^\varepsilon.
$$
式 (22) 的第二项有至多 $D_0^3\le X^{3/2}$ 个模数组合。因此全匹配的总贡献 $\ll_\varepsilon X^{9/2+\varepsilon}$。该界对带内任意可测子区的绝对贡献均成立，特别覆盖前稿 $\Omega_X$ 的不规则截边。



## 一个未匹配标签的成本与真正的驻点

<small>原稿第 11 页</small>

若五个标签可匹配，剩余负位置的模数由上面的偶数性固定。其特征、纵坐标和重数的选择至多 $O(\varphi(q)B L)\ll\sqrt X L^2$。未匹配正位置仍可用第 10 页的重数平方上界。因此
$$
 \boxed{\quad
 \begin{aligned}
  \text{六个标签匹配的总贡献}&\ll_\varepsilon X^{9/2+\varepsilon},\\
  \text{至少五个标签匹配的总贡献}&\ll_\varepsilon X^{5+\varepsilon}.
 \end{aligned}\quad}                                                   \tag{23}
$$
更一般地，若两侧模数多重集相同，且所有未匹配负标签的 $q(1+|\gamma|)$ 二进尺度之积 $\le X^{1-\delta}$，则同一证明给 $O_{\delta,\varepsilon}(X^{11/2-\delta+\varepsilon})$。取 $\varepsilon<\delta$ 即达标。对四个匹配而两个自由标签均在最大尺度的情形，以上论证尚无严格的幂次余量。

**一个实际零点给出的驻相配置。** 取 $\zeta$ 的负零点纵坐标 $\gamma\to-\infty$，令 $X=|\gamma|^{10}$，并取 $X^{2/5}<q<2X^{2/5}$ 的素数。在六个局部块中分别选择模 $q$ 的分子
$$
 (1,4,12\,;\,2,6,9),\qquad 1+4+12=2+6+9 .
$$
选 $z=3/2$，两腿 $u=v=3/4$，$\beta=-2\gamma/(3\pi X)$，各自的加法频率为 $a_i/q+\beta$。这些点都落在小弧，因为 $1/(qQ)\gg|\beta|+L^4/X$。任意两点之和或差距半整数 $\gg1/q$，且 $\Delta=0$。因此这组点位于 $\Omega_X$。它们同时满足 Dirichlet 逼近的宽度条件。需要选定局部块时可在这些中心的邻域优先采用相应逼近。

取模 $q$ 的主特征，$L(s,\chi_0)=\zeta(s)(1-q^{-s})$ 确实有这个零点，且每个既约分子的 Gauss 系数为 $-1$。各腿用同一纵坐标，(12) 真有驻点，外层又有 $T=\Theta=0$。这是 (23) 已控制的一个配置。它也说明仅凭几何分离无法在整片余区继续分部积分。真正未决的是 (9)，包括未被 (23) 或其推广覆盖的高度、标签和模数组合及其交叉项。




## 在原来的共振截边上精确消去非主特征

<small>原稿第 12 页</small>

对 $Q<q\le D_0$，取对称小弧子区 $\alpha=a/q+\beta$，$|\beta|\le 1/(8qD_0)$。所有既约分子都用相同宽度。不同中心的距离至少 $1/(qq')$，因而这些区间彼此不交。它们也完全落在小弧，因为对主弧中心的距离至少 $1/(qQ)$，显著大于 $L^4/X$ 与该子区半宽之和。可以在这些区间上优先选取相应的 Dirichlet 逼近。

固定六个模数 $q_i$ 和六个偏移 $\beta_i$，令 $K=\operatorname{lcm}(q_1,\ldots,q_6)$。沿用前稿微观宽度常数 $b_0$。若
$$
   K\left(\sum_i|\beta_i|+(L^4+b_0)/X\right)<\tfrac12 ,               \tag{24}
$$
则 $\Omega_X$ 上的六分子和，对总特征非主的每一项**精确等于零**。六个模数相同时 (24) 对上述子区自动成立。各模数不同但满足 (24) 时同样适用。

**证明。** 在每个位置将两条腿的单位类部分按特征 $\chi_{i,1},\chi_{i,2}$ 展开。既约分子只通过 $\tau_{a_i}(\bar\chi)=\chi(a_i)\tau_1(\bar\chi)$ 出现。任取 $u\in(\mathbb Z/K\mathbb Z)^\times$ 同时将 $a_i$ 改为 $ua_i\bmod q_i$。所有固定的有理和与差都在 $K^{-1}\mathbb Z/\mathbb Z$ 中，该网格的非半整数点距最近半整数至少 $1/(2K)$。故由 (24)，集体共振和微观边都先要求相应的有理中心**恰为半整数**，其后只检验固定的 $\beta_i$。乘单位 $u$ 保持半整数子群及其补集。在集体共振内，$D_W$ 的周期为 $1/2$，故核也保持原值。

设六分子和为 $Z$，$\epsilon_i=1$（前三个）或 $-1$（后三个）。上述置换给
$$
 Z=\Xi(u)Z,\qquad
 \Xi(u)=\prod_{i=1}^6
       \big(\chi_{i,1}(u)\chi_{i,2}(u)\big)^{\epsilon_i}.             \tag{25}
$$
若 $\Xi$ 在模 $K$ 单位群上非主，取 $\Xi(u)\ne1$ 即得 $Z=0$。此论证在乘法扭和展开后已经成立，亦适用于各个 Mellin 零点项。总特征为主、(24) 以外的块，以及对称子区之间的空隙均须在总体估计中处理。

对原来的两条素数腿，若在整个小弧按选定的 $q$ 删去非单位项，每条腿的点态改变量 $\ll L^2$（只含 $p\mid q$ 的素数幂）。乘积差的 $L^2$ 范数 $\ll L^2(\|P_y\|_2+\|P_\eta\|_2+L^2)\ll\sqrt X L^{5/2}$。由 Parseval 与 $\ell^6\le\ell^2$，在完整带窗系数矩上这项差的六阶矩 $\ll X^3L^{15}$。单独的 Type II 系数可能在非单位上有不同的支撑，前一估计只用于原来的素数腿。

### 文献与核验

[1] [前稿《哥德巴赫六阶矩的主弧与共振小弧》](07-arcs.md)，式 (4)、(6)、(10)、(12) 至 (15)。  
[2] [Davenport，Multiplicative Number Theory](https://link.springer.com/book/9780387950976)，第 16 章的局部零点展开。  
[3] [Vaughan 恒等式与 Type I、II 卷积](https://terrytao.wordpress.com/2015/01/10/254a-notes-3-the-large-sieve-and-the-bombieri-vinogradov-theorem/)。  
[4] [Vasy，Stationary phase lemma](https://math.stanford.edu/~andras/205C-2.pdf)。[Friedlander–Goldston](https://doi.org/10.1090/S0002-9947-97-01652-8)，§7 给出素数指数和的一变量 Mellin 振荡核。

配套 Lean 文件核验有限正交、矩插值、留数极限、相位导数、最小公倍数分组及有限群置换抵消。GRH、Perron 移线和连续驻相估计使用文中的解析证明。式 (9) 是未决的算术估计。
