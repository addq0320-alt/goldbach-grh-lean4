# 哥德巴赫六阶矩的主弧与共振小弧

<small>原稿第 1 页</small>

令 $D_X=\{n\in[X,2X]:2\mid n\}$，$L=\log(2X)$，$I=(1/3,2/3)=(a,b)$。全篇假设 Dirichlet $L$ 函数的 GRH。沿用前稿的真实平衡区间压缩 $B_n$ 及奇异级数 $S_n$。其中心化测度、Hilbert–Schmidt 能量与未取平均的六阶矩为
$$
 \sigma_n=du-\frac1{nS_n}\sum_{\substack{m/n\in I\\(m,n)=1}}
       \Lambda(m)\Lambda(n-m)\delta_{m/n},\qquad
 \mathcal M_X=\sum_{n\in D_X}\|A_{\sigma_n}\|_{\rm HS}^6 .
$$
这里 $A_\nu$ 对应 $H_0^1(I)$ 上的型 $\int f\bar g\,d\nu$。前稿已证 $R_X\ll X^{-1/2}L^{12}$ 与 $\mathcal M_X\ll X^{-1/2}L^{12}$ 等价，两者任一即推出 $\max_{n\in D_X}\|B_n\|/S_n\ll X^{-1/12}L^2$。[1]

**主弧定理。** 取 $Q=\lfloor X^{3/10}\rfloor$。围绕所有既约 $a'/q$、$q\le Q$ 在圆上取半宽 $L^4/X$ 的主弧 $\mathfrak M$，其余为 $\mathfrak m$。第 2 页定义真实算术弧测度 $\lambda_n^{\mathcal A}$。对任意固定 $\varepsilon>0$，
$$
 \boxed{\displaystyle
 \sum_{n\in D_X}\|A_{du-\lambda_n^{\mathfrak M}}\|_{\rm HS}^6
      \ll_\varepsilon X^{-4/5+\varepsilon}.} \tag{1}
$$
这个界控制主弧扣除完整奇异级数后的误差。若希望在小分母处加宽主弧，改取 $Q=\lfloor X^{8/29}\rfloor$ 和半宽 $(L^4+X^{7/29}/q)/X$，右端可取 $X^{-19/29+\varepsilon}$。两组参数均在原目标之内。

**小弧定理。** 将一个足以推出原目标的小弧判据写成六频积分。Poisson 求和将六个加法频率的有符号和限制在半整数的 $O(L^4/X)$ 邻域。在此共振邻域内，只要六个频率中出现两条不同的 $O(1/X)$ 接近关系，该区域就满足目标界；两条关系可以共用一个顶点。余下的单侧上界仍未证明。

两处“小频率”作用不同。前稿 $F_n(0)$ 中的零是区间权的 Mellin 频率；使用该权时，本稿的加法小弧仍然出现。



## 保持真实算术测度的圆法分拆

<small>原稿第 2 页</small>

写 $e(t)=\exp(2\pi it)$，$\widehat H(j)=\int_{\mathbb T}H(\alpha)e(-j\alpha)d\alpha$，圆上测度总质量为一。取实非负 $\eta\in C_c^\infty((1/8,2))$，在 $[1/3,4/3]$ 恒为一，且其连续傅里叶变换满足 $|\widehat\eta(v)|\ll e^{-c\sqrt{|v|}}$。令
$$
 \begin{aligned}
 P_y(\alpha)&=\sum_{1\le m\le y}\Lambda(m)e(\alpha m),&
 V_y(\beta)&=\int_0^y e(\beta t)\,dt,\\
 P_\eta(\alpha)&=\sum_{j\ge1}\Lambda(j)\eta(j/X)e(\alpha j),&
 V_\eta(\beta)&=\int_{\mathbb R}\eta(t/X)e(\beta t)\,dt .
 \end{aligned}
$$
对对称弧集 $\mathcal A$，定义实符号测度
$$
 \lambda_n^{\mathcal A}
 =\frac1{nS_n}\sum_{m/n\in I}\Lambda(m)
     \widehat{\mathbf1_{\mathcal A}P_\eta}(n-m)\,\delta_{m/n}.
 \tag{2}
$$
当 $m/n\in I$，有 $(n-m)/X\in[1/3,4/3]$。正交性因而给出
$\sigma_n=du-\lambda_n^{\mathfrak M}-\lambda_n^{\mathfrak m}+\kappa_n$，其中 $\kappa_n$ 为互素条件舍去的正测度。其总变差 $\ll L^3/X$。事实上，有权且 $(m,n)>1$ 的 $m$ 必为 $p^k$，$p\mid n$；每个 $p$ 的 $\Lambda(m)$ 总和至多 $L$，另一因子至多 $L$，且 $\omega(n)\ll L$，$S_n\gg1$。互素修正仅在两弧相加后处理。

**平滑权构造。** 取 $a_j=c_0/j^2$，使 $\sum_{j\ge1}a_j<1/48$。独立的 $[-a_j,a_j]$ 上均匀变量之和的分布 $\rho$ 支撑于 $[-1/48,1/48]$。当 $|v|$ 大时，积 $\widehat\rho(v)=\prod_j\sin(2\pi a_j v)/(2\pi a_j v)$ 的前 $\lfloor c_1\sqrt{|v|}\rfloor$ 项模长至多 $1/2$。于是 $\rho$ 有光滑密度和所需的傅里叶衰减。可取 $\eta=\mathbf1_{[1/4,3/2]}*\rho$。后文用于偶数求和的权取 $W=\mathbf1_{[3/4,9/4]}*\rho$，它在 $[1,2]$ 恒为一。

对 $0\le y\le2X$ 置 $I_n(y)=\int_0^y\eta((n-t)/X)\,dt$。需要控制的主弧截点误差为
$$
 E_y(n)=\widehat{\mathbf1_{\mathfrak M} P_yP_\eta}(n)-S_n I_n(y). \tag{3}
$$
截点 $y$ 固定后，两个素数指数和都与 $n$ 无关。这使对 $n$ 求均方时可直接用 Parseval。



## 同分母正交与线性误差

<small>原稿第 3 页</small>

允许半宽 $Z_q/X$ 依赖分母，且所有弧互不相交。置 $\lambda_q=\mu(q)/\varphi(q)$。对 $j=y,\eta$，在 $\alpha=a'/q+\beta$ 写
$P_j(\alpha)=\lambda_q V_j(\beta)+D_j(a',q,\beta)$。若 $U=1+X|\beta|$，则有一致估计
$$
 \sum_{a'\bmod q}^{*}|D_j(a',q,\beta)|^2\ll qX L^4 U^2. \tag{4}
$$

**证明。** 在单位剩余类 $r$ 上，从带 $\Lambda$ 的和扣掉 $V_j/\varphi(q)$，记结果为 $d_r$。其乘法特征变换为 $\Lambda\chi$ 的加性扭和减去 $\mathbf1_{\chi=\chi_0}V_j$。GRH 给出 $\psi(t,\chi)-\mathbf1_{\chi=\chi_0}t\ll\sqrt t\log^2(2qt)$。分部求和后，每个变换值 $\ll\sqrt X L^2U$，对实截点及固定光滑权均成立。[2]

乘法 Parseval 给 $\sum_r|d_r|^2\ll XL^4 U^2$。将 $d_r$ 在非单位类延拓为零，再作加法变换；对所有分子求平方和恰得 $q\sum_r|d_r|^2$。保留既约分子只会降低平方和。单位类主项变为 $\lambda_q V_j$，因为 $c_q(a')=\mu(q)$。非单位类至多贡献 $\sum_{p\mid q,k:p^k\le2X}\log p\ll L^2$ 于每个分子。这证明 (4)。

两乘积相减后，设线性项为 $H_1=\lambda_q(V_yD_\eta+V_\eta D_y)$，二次项为 $H_2=D_yD_\eta$，弧外取零。定义
$$
 U_1=\sum_{q\le Q}\frac q{\varphi(q)}Z_q,\quad
 U_2=\sum_{q\le Q}\frac q{\varphi(q)^2}Z_q,\quad
 U_3=\sum_{q\le Q} q Z_q^3 .
$$
全篇取 $Z_q\ge1$。由 $|V_j|\ll X/U$ 及 (4)，先在同一分母对分子作 Cauchy–Schwarz，再对 $\beta$ 积分，得
$$
 \|\widehat H_1\|_\infty\ll\sqrt X L^2 U_1,\qquad
 \sum_{n\in\mathbb Z}|\widehat H_1(n)|^2\ll X^2 L^4 U_2,\qquad
 \|\widehat H_2\|_\infty\ll L^4 U_3. \tag{5}
$$
中式用弧不交及圆上 Parseval。末式在每个 $\beta$ 先对两个误差的分子向量用 Cauchy–Schwarz，再用 $\int_{-Z_q/X}^{Z_q/X}U^2d\beta\ll Z_q^3/X$。



## 完整奇异级数与三项指数

<small>原稿第 4 页</small>

模型乘积的第 $n$ 个系数为
$$
 \sum_{q\le Q}\frac{\mu(q)^2 c_q(n)}{\varphi(q)^2}
   \int_{|\beta|\le Z_q/X}V_y(\beta)V_\eta(\beta)e(-n\beta)d\beta .
$$
对每个分母将积分延至整条实线，傅里叶反演给出 $I_n(y)$。取 $Z_q\ge L^4$；由 $V_\eta(\beta)=X\widehat\eta(-X\beta)$，截去实尾的误差对每个分母都是 $O_A(X^{-A})$，任意固定 $A$ 可用。奇异级数的绝对值尾满足
$$
 \sum_{q>Q}\frac{\mu(q)^2|c_q(n)|}{\varphi(q)^2}\ll_\varepsilon \frac{X^\varepsilon}{Q}.
$$
确实，对无平方因子 $q=dm$ 取 $d=(q,n)$，则 $|c_q(n)|=\varphi(d)$。放宽互素与无平方因子限制后，先用 $\sum_{m>v}1/\varphi(m)^2\ll_\varepsilon v^{-1+\varepsilon}$，再用 $\sum_{d\mid n}d/\varphi(d)\ll_\varepsilon X^\varepsilon$，并重取 $\varepsilon$。模型误差因此为 $O_\varepsilon(X^{1+\varepsilon}/Q)$，对所有 $n,y$ 成立。

用 $\sum|\widehat H_1|^6\le\|\widehat H_1\|_\infty^4\sum|\widehat H_1|^2$，结合 (5) 得到
$$
 X^{-6}\sup_y\sum_{n\in D_X}|E_y(n)|^6
 \ll_\varepsilon X^\varepsilon
 \left(\frac X{Q^6}+\frac{U_1^4 U_2}{X^2}+\frac{U_3^6}{X^5}\right). \tag{6}
$$
三项依次来自奇异级数尾、线性误差和二次误差。对于等宽弧，$U_1\ll_\varepsilon X^\varepsilon QZ$，$U_2\ll_\varepsilon X^\varepsilon Z$，$U_3\ll Q^2Z^3$。取 $Q=X^{3/10}$、$Z=L^4$，三项的幂次依次为 $-4/5,-4/5,-7/5$。亦可取 $Q=X^{4/15}$、$Z=X^{1/15}$，三项均为 $-3/5$。

若 $Q=X^\theta$，$Z_q=L^4+X^\gamma/q$，忽略可吸收到 $X^\varepsilon$ 的因子，$U_1\ll Q+X^\gamma$，$U_2\ll1+X^\gamma$，$U_3\ll Q^2+X^{3\gamma}$。取 $\theta=8/29,\ \gamma=7/29$，三项均为 $X^{-19/29}$。所有这些弧都不交，因为分数间距至少 $1/(qq')$，且变宽方案有 $Q^2L^4+QX^\gamma=o(X)$。整数截点取整不影响估计。



## 将主弧界送回原来的算子

<small>原稿第 5 页</small>

对有限实符号测度 $\nu$ 写 $D_\nu(u)=\nu((a,u])$。有一致估计
$$
 \|A_\nu\|_{\rm HS}^6\ll \int_I |D_\nu(u)-c|^6du\qquad(c\in\mathbb R).
 \tag{7}
$$
导数将 $H_0^1(I)$ 等距送到零均值 $L^2(I)$。在该子空间上算子核是 $\nu(I)-D_\nu(\max(s,t))$ 的压缩，端点约定只相差二维零测集。常数核在压缩后消失，以此得 $\|A_\nu\|_{\rm HS}^2\ll\int_I|D_\nu-c|^2$，再用 Hölder 即得 (7)。[1]

对于 $\nu=du-\lambda_n^{\mathfrak M}$，$D_\nu(u)$ 与 $-E_{nu}(n)/(nS_n)$ 只差一个与 $u$ 无关的常数。这是因为 $I_n(nu)-I_n(na)=n(u-a)$。选去该常数，在 (7) 中作 $y=nu$ 的换元，得到
$$
 \sum_{n\in D_X}\|A_\nu\|_{\rm HS}^6
 \ll X^{-7}\int_0^{2X}\sum_{n\in D_X}|E_y(n)|^6dy .
$$
左端按 $n$ 取相应的测度 $\nu$。由 (6) 即得主弧定理。互素修正满足 $\|A_{\kappa_n}\|_{\rm HS}\ll\|\kappa_n\|_{\rm TV}$。用 $\ell^6$ 中的三角不等式，对等宽对数方案有
$$
 \left|\mathcal M_X^{1/6}-
    \left(\sum_{n\in D_X}\|A_{\lambda_n^{\mathfrak m}}\|_{\rm HS}^6\right)^{1/6}\right|
     \ll_\varepsilon X^{-2/15+\varepsilon}. \tag{8}
$$
所以就原目标尺度而言，$R_X$ 的单侧上界与真实小弧测度的 Hilbert–Schmidt 六阶矩上界等价。这里先还原到前稿的完整能量，避免对截去近对角线的带符号六重积逐因子换弧。

**可进一步计算的充分条件。** 固定 $y$，令 $H_y=\mathbf1_{\mathfrak m}P_yP_\eta$，$C_y(n)=\widehat H_y(n)$。再用 (7) 和同一换元可知，只要
$$
 \sup_{0\le y\le2X}\ \sum_{n\in D_X}|C_y(n)|^6\ll X^{11/2}L^{12}, \tag{9}
$$
便得到原目标。取截点上确界加强了条件；(8) 给出的等价命题保留实际 Hilbert–Schmidt 能量。



## Poisson 求和留下哪一种共振

<small>原稿第 6 页</small>

使用第 2 页的 $W$，以 $\sum_{n\in2\mathbb Z}W(n/X)|C_y(n)|^6$ 上界 (9) 左端的单个截点和。写 $\mathbf t=(t_1,\ldots,t_6)$，
$\Delta=t_1+t_2+t_3-t_4-t_5-t_6$。这个非负和精确等于
$$
 \int_{\mathbb T^6} \prod_{j\le3}H_y(t_j)
       \prod_{j>3}\overline{H_y(t_j)}\,D_W(\Delta)\,d\mathbf t,\qquad
 D_W(v)=\sum_{n\in2\mathbb Z}W(n/X)e(-nv). \tag{10}
$$
Poisson 求和给 $D_W(v)=\frac X2\sum_{h\in\mathbb Z}\widehat W(X(v-h/2))$。特别是 $\|D_W\|_{L^1(\mathbb T)}\ll1$。在 $\operatorname{dist}(v,\tfrac12\mathbb Z)>L^4/X$ 时，指数衰减给出 $D_W(v)=O_A(X^{-A})$。因 $\|H_y\|_1\ll XL$，(10) 在该区域的积分也为 $O_A(X^{-A})$。半整数共振中的 $1/2$ 来自只对偶数求和。

第二个结果直接描述小弧系数的带符号平均。在变宽方案中，对既约 $a'/r$，$r\le Q/2$，任取 $W_0\in C_c^\infty(\mathbb R)$、实数 $n_0$ 和 $H\le X$。若 $H\ge rX^{22/29+\delta}$，其中 $\delta>0$ 固定，则
$$
 \sum_{n\in2\mathbb Z} W_0((n-n_0)/H)e(na'/r)\,C_y(n)
       =O_{A,\delta,W_0}(X^{-A}). \tag{11}
$$
这是未归一化的和。确实，$a'/r$ 与 $a'/r+1/2$ 的既约分母均至多 $2r$；小弧到二者的距离至少为 $X^{-22/29}/(2r)$。Poisson 核在此处至多为 $O_B(H(1+H X^{-22/29}/(2r))^{-B})$。乘 $\int|P_yP_\eta|\ll XL$，并将 $B$ 取充分大即得。平移 $n_0$ 只引入单位相位。

式 (11) 对线性平均成立。六阶矩涉及绝对值的六次方，Poisson 后保留的是 (10) 的集体相位。这也解释了低分母线性平均为什么可以远小于高阶矩。

**为何还需要真实的素数系数。** 固定任一 $n_0\in D_X$，在同一小弧上取辅助函数 $G(\alpha)=X e(n_0\alpha)\mathbf1_{\mathfrak m}(\alpha)$。因为 $|\mathfrak M|=o(1)$，故 $|\widehat G(n_0)|=(1-o(1))X$，该项单独对六阶矩贡献 $(1-o(1))X^6$。另一方面 $\|G\|_1\le X$、$\|G\|_2^2\le X^2$、$\|G\|_\infty\le X$，且 (11) 的 Poisson 论证同样适用。它验证了仅凭频率支撑、这些范数及平滑带符号平均，无法推出 (9)；需要额外利用 $P_yP_\eta$ 的算术结构。



## 控制共振所需的三个小弧范数

<small>原稿第 7 页</small>

在前述三组弧中，$Q\ge X^{1/4+\delta_0}$ 对某个固定 $\delta_0>0$，且 $Z_q\ge L^4$。对所有 $y\le2X$，
$$
 \boxed{\quad
 \|H_y\|_1\ll XL,\qquad
 \|H_y\|_2^2\ll X^{5/2}L^4,\qquad
 \|H_y\|_\infty\ll X^{3/2}L^3 .\quad} \tag{12}
$$
第一式由 Parseval、Cauchy–Schwarz 及 $\sum_{j\le2X}\Lambda(j)^2\ll XL$ 得到。后二式需要保留加法扭和的局部误差。[3]

对每个 $\alpha$ 使用 Dirichlet 逼近 $\alpha=a'/s+\beta$，其中 $s\le D=\lfloor\sqrt X/L\rfloor$，$|\beta|\le1/(sD)$。写 $B=X|\beta|$。Friedlander–Goldston 式 (1.15) 在 GRH 下给出两个素数和在该点扣去 $\lambda_s V_j$ 后的误差
$$
 |D_j|\ll \sqrt{sX}\,L(L+\sqrt B)=:\mathcal E,\qquad
 \mathcal E\ll X^{3/4}L^{3/2}\quad(j=y,\eta).
$$
第一式中的常数已吸收在 $\ll$ 内。对截点使用原式；$y<s$ 时用平凡界。对光滑权作分部求和。素数换成 $\Lambda$ 的高次幂误差、几何级数与连续积分之差，均在上述界内。[3，式 (1.15)、(2.7)]

在小弧上，若 $s\le Q$，则 $B\ge L^4$，故光滑主项 $|\lambda_s V_\eta|$ 小于任意负幂；若 $s>Q$，它至多是 $X/\varphi(s)\ll X^{3/4}$，这里用了 $Q$ 的严格幂次余量。因此 $\sup_{\mathfrak m}|P_\eta|\ll X^{3/4}L^{3/2}$，乘以 $\|P_y\|_2$ 得中式。

对乘积的一致界，两误差相乘至多 $\mathcal E^2$。光滑主项乘任一误差也已满足目标。另一个交叉项使用局部尺度而非全局最大值，
$$
 |\lambda_s V_y|\,\mathcal E
 \ll X^{3/2}\frac{\sqrt s}{\varphi(s)}
        \frac{L(L+\sqrt B)}{1+B}\ll X^{3/2}L^2 .
$$
两个主项相乘在 $s\le Q$ 时快速衰减；在 $s>Q$ 时有 $O(X^2/\varphi(s)^2)\ll X^{3/2}$。合并即得最后一式。保留对数的具体次数，使下一页两种配置都恰好落在 $L^{12}$ 的预算内。



## 共振中有两条接近关系的部分

<small>原稿第 8 页</small>

为简明以 $H=|H_y|$ 表示振幅，并固定宽度常数 $b_0>0$。在六个频率的两个不同位置 $i,j$ 间连边，条件取
$$
 \|t_i\pm t_j-c\|_{\mathbb T}\le b_0/X,\qquad c\in\{0,1/2\}.
$$
对包含至少两条不同无向边的区域，(10) 的绝对贡献 $\ll_{b_0}X^{11/2}L^{12}$，对 $y$ 一致。该界在集体共振内仍成立。证明只需讨论两种图形。

**两边没有共同顶点。** 一个受约束的对子积分 $\ll X^{-1}\|H\|_2^2$，因为确定平移或反射偏差以后，余下的一维相关由 Cauchy–Schwarz 上界。对没有受约束的最后两点，保留已经把 $n$ 的相位相加的核 $D_W$。其积分对其余相位一致地至多 $\|D_W\|_1\|H\|_2^2$，这是固定最后一对的和或差后再用同一不等式。因此
$$
 |\text{贡献}|\ll X^{-2}\|H\|_2^6\ll X^{11/2}L^{12}. \tag{13}
$$

**两边有一个共同顶点。** 固定两个偏差，三点相关由 $\|H\|_\infty\|H\|_2^2$ 控制。积分两个偏差给出 $X^{-2}$。对另外三点，先固定一点，再用上面带 $D_W$ 的二点积分，成本为 $\|H\|_1\|H\|_2^2$。从而
$$
 |\text{贡献}|\ll X^{-2}\|H\|_\infty\|H\|_1\|H\|_2^4
        \ll X^{11/2}L^{12}. \tag{14}
$$
边、符号、中心的选择个数固定，有限并不改变数量级。以上绝对值估计只在 Poisson 对偶核已经形成后使用；直接以 $\sup|D_W|\asymp X$ 替换其 $L^1$ 范数会丢掉整个幂次。

**未决单侧估计。** 令 $\Omega_X$ 为 $\mathfrak m^6$ 内同时满足 $\operatorname{dist}(\Delta,\frac12\mathbb Z)\le L^4/X$ 和至多一条上述微观边的集合。令 $J_y$ 为 (10) 在 $\Omega_X$ 上的带符号积分。根据 (10)、(13)、(14)，证明
$$
 \sup_{0\le y\le2X}\operatorname{Re}J_y\ll X^{11/2}L^{12} \tag{15}
$$
即足以推出原 $R_X$ 上界。若在余区仅用 $\|D_W\|_1$ 与 (12)，得到的是 $\|H\|_2^2\|H\|_1^4\ll X^{13/2}L^8$。这里尚差一个 $X$ 的幂次。第 6 页的相位对齐例子在剔除上述两个可控区域后仍有 $\gg X^6$ 的贡献；式 (15) 因而需要真实素数相位的抵消。



## 对偶空间中真正的 Kloosterman 和

<small>原稿第 9 页</small>

圆法一开始的分子和是 $c_q(n)$。在 Vaughan 分解的一类 Type I 块内，可对光滑的无权变量作 Poisson 求和以产生倒数相位。令 $U\in C_c^\infty((0,\infty))$，$M>0$；$c_d,b_j$ 是有限支撑系数。保留 $(d,q)=1$ 的子块，以 $a'/q+\beta$ 代入两因子。共同相位为 $e((dm+j-n)(a'/q+\beta))$。对 $m$ 作 Poisson，再对既约分子 $a'$ 求和，该子块精确等于
$$
 M\sum_j b_j e((j-n)\beta)
 \sum_{\substack{h\in\mathbb Z\\(h,q)=1}}\ 
 \sum_{(d,q)=1} c_d\,
 \widehat U\bigl(M(h/q-\beta d)\bigr)\,
 e\!\left(\frac{(n-j)h\bar d}{q}\right). \tag{16}
$$
其中左边的子块包含 $\sum_m U(m/M)$ 及所述相位。恒等式来自 $h\equiv-a'd\pmod q$，故 $a'\equiv-h\bar d\pmod q$。当另一个素数因子依赖分子时，倒数相位中的参数正是 $n-j$。在按既约分母取相同弧截点的块中，可在积分前使用此恒等式；若另外的划分使权依赖 $a'$，该权也须随同保留。

固定 $h,\beta$，把 $d$ 的权按 $d\bmod q$ 合并为 $b(r)$，在非单位类取零。用未归一化的负号有限变换 $\widehat b(k)$，则
$$
 \sum_{r\bmod q}^{*} b(r)e(t\bar r/q)
 =\frac1q\sum_{k\bmod q}\widehat b(k)S(k,t;q),\qquad t=(n-j)h .
$$
Weil 界为 $|S(k,t;q)|\le\tau(q)\sqrt{q(k,t,q)}$。在 $q\mid n-j$ 且 $k=0$ 时，$S(0,0;q)=\varphi(q)$。即使 $(n-j,q)=1$，逐个应用 Weil 界后还带有 $\tau(q)q^{-1/2}\sum_k|\widehat b(k)|$。对任意权，Parseval 只能将后者估到 $\tau(q)\sqrt q\,\|b\|_2$。降到 (15) 需要跨变量、模数以及 Type II 块的额外抵消。[4]

恒等式 (16) 给出可尝试 Deshouillers–Iwaniec 谱大筛的实际变量。六个加法频率的集体共振本身只有一条线性关系，微观分离也不会产生 Vinogradov 中值定理所需的多次幂相位系统。将这些结果用于 (15) 还需要具体的多线性估计及参数核算。



## Mellin 变换、零点与绝对值的代价

<small>原稿第 10 页</small>

对光滑因子，令 $V_\beta(s)=\int_0^\infty\eta(u)e(X\beta u)u^{s-1}du$，$\tau_{a'}(\bar\chi)=\sum_{r\bmod q}^{*}\bar\chi(r)e(a'r/q)$。在 $\sigma>1$ 上，乘法特征正交与 Mellin 反演给出
$$
 P_\eta(a'/q+\beta)=\frac1{\varphi(q)}
 \sum_{\chi\bmod q}\tau_{a'}(\bar\chi)
 \frac1{2\pi i}\int_{(\sigma)}
      -\frac{L'}{L}(s,\chi)X^s V_\beta(s)\,ds+O(L^2).
$$
余项是 $p\mid q$ 的素数幂。对 $s=\sigma+it$，振荡相位导数为 $2\pi X\beta+t/u$。在支撑上若该导数的模一致大于 $c(1+|t|+X|\beta|)$，反复分部积分给任意阶衰减。若 $|t|\asymp X|\beta|\ge1$ 且有驻点，二阶导数界给 $V_\beta(s)\ll_{\sigma,\eta}|t|^{-1/2}$。GRH 确定非平凡零点的实部；出现两个素数因子的零点乘积时，还需保留余下的相位。已知含双重零点和的 Cesàro 显式公式对表示整数另作了平均。[5]

**整个小弧上取绝对值的实际大小。** 在等宽对数方案中，令两个素数和均取 $P_\eta$。则
$$
 \int_{\mathfrak m}|P_\eta(\alpha)^2|\,d\alpha
 = (1-3/10+o(1))\,X\log X\int_{\mathbb R}\eta(u)^2du .
$$
整圆由 Parseval 和素数定理给主项 $X\log X\int\eta^2$。主弧模型的平方积分为 $(\log Q+O(1))X\int\eta^2$，因为 $\sum_{q\le Q}\mu(q)^2/\varphi(q)=\log Q+O(1)$。该级数的 Dirichlet 函数除以 $\zeta(s+1)$ 后，欧拉因子为 $1+(p^{-s}-p^{-2s})/[p(p-1)]$，在 $\Re s>-1/2$ 绝对收敛，且 $s=0$ 取一。由 (4)，主弧误差平方积分 $\ll Q^2 L^{16}=o(X)$，交叉项由 Cauchy–Schwarz 为 $o(X\log X)$。所以即使在这个光滑例子，整片小弧逐点取绝对值仍保留了主量级。

### 文献与核验

[1] 前稿的原始能量与 $R_X$ 的比较。[GoldbachDuality.pdf](06-duality.md)  
[2] Montgomery–Vaughan，*Multiplicative Number Theory I*，第 13 章；[GRH 下的特征和显式估计，定理 6.1](https://kokunoyumeto.github.io/open-math-courses-public/courses/NT-DIRL/NT-DIRL-08.html)。  
[3] Friedlander–Goldston，*Sums of Three or More Primes*，式 (1.15)、(2.7)。[原论文](https://doi.org/10.1090/S0002-9947-97-01652-8)  
[4] J. Jung、N. Sardari，[一般模数 Weil 界，式 (2.7)](https://pure.mpg.de/rest/items/item_3252519_4/component/file_3252520/content)；S. Drappeau，[Mémoire HDR，§1.1](https://drappeau.perso.math.cnrs.fr/documents/hdr-eng.pdf)。  
[5] Languasco–Zaccagnini，*A Cesàro Average of Goldbach Numbers*。[原论文](https://arxiv.org/abs/1206.0251)

附带源文件通过 Lean 4.19.0 的内核及公理检查，覆盖 23 条定理，包括有限模数的分子正交、Parseval、带窗六阶矩、倒数和的补全与退化情形、矩插值、接近频率的相关、单个系数的相位对齐和参数指数。GRH 输入、连续 Poisson 及上述解析界采用本文的数学证明。式 (15) 保留为待证命题。
