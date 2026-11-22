# 哥德巴赫算子在短区间内的平均

<small>原稿第 1 页</small>

沿用李–刘算子的平衡压缩 $B_n$，其中 $n$ 为偶数，$I=(a,b)=(1/3,2/3)$，$S_n=\mathfrak S(n)$。本文假设全体 Dirichlet $L$ 函数的 GRH。定理 2 的素数对结论只用黎曼 $\zeta$ 函数的 RH。下文取充分大的整数 $M$、$L=\log(2M)$ 及整数 $1\le h\le\sqrt M$，置

$$
 w_h(j)=\frac{(h-|j|)_+}{h^2}\quad(j\in\mathbb Z),\qquad
 \sum_j w_h(j)=1.
$$

**定理 1。** 用同一个测试空间 $H_0^1(I)$ 比较不同偶数，把 $B_n$ 拉回成 $\widetilde B_n=W_n^* B_nW_n$。在每个这样的窗口内都有

$$
 \boxed{\quad
 \left\|\sum_{2\mid n} w_h(n-M)\widetilde B_n\right\|_{\rm HS}
       \ll \frac{L^2}{h}.\quad} \tag{1}
$$

$W_n f=v_{\bar f}$ 为 Mellin 测试向量映射，$W_n$ 及其逆的范数对 $n$ 一致有界。式 (1) 先对算子求和再取范数。因而当 $h/L^2\to\infty$ 时，每个窗口的有符号平均都趋于零。单从这种平均不能估计每一项的范数。例如偶数上取 $D_n=(-1)^{n/2}A$、奇数上取零，$4\mid h$ 时三角加权和为零，而每个偶数项都有范数 $\|A\|$。

**定理 2。** 给定非空开区间 $J\Subset I$，存在 $C_J,c_J>0$。若 $C_J L^2\le h\le\sqrt M$，则 $(M-h,M+h)$ 至少有 $c_Jh$ 个偶数 $n$ 满足

$$
 \#\{(p,q):p,q\text{ 为素数},\ p+q=n,\ p/n\in J\}
       \ \ge\ c_J\,\frac{n S_n}{(\log n)^2}. \tag{2}
$$

这给出每个对数平方长度窗口内有多少偶数具备预期数量级的局部表示。前篇给出全区间 $[X,2X]$ 的平方根例外集界，对例外集在短区间里的聚集则没有约束。这里采用 Goldston 的三角权思想，在平衡区间的每个截点保持一致，并与上界筛结合。[1–3]

**真实算子的识别。** 对偶数定义
$\nu_n=n^{-1}\sum_{m/n\in I,\ (m,n)=1}\Lambda(m)\Lambda(n-m)\delta_{m/n}$、
$\rho_n=S_n\,du-\nu_n$。前篇的混合型恒等式给出 $\widetilde B_n=A_{\rho_n}\mathcal R$，其中 $A_\rho$ 在导数范数的 $H_0^1(I)$ 上对应 $\int f\bar g\,d\rho$，$\mathcal Rf(u)=f(1-u)$。对任意有限实符号测度有

$$
 \|A_\rho\mathcal R\|_{\rm HS}\ll
   \left(\int_a^b |\rho((a,u])|^2du\right)^{1/2}.
$$

因为取导数后，算子核由 $\rho(I)-\rho((a,\max(s,t)])$ 压缩到零均值子空间，常数核在该空间上消失。故只需一致地估计平均测度在 $(a,u]$ 上的值。[前篇式 (2)](04-farey.md)



## 两个短素数和与三角权

<small>原稿第 2 页</small>

置 $\psi(t)=\sum_{m\le t}\Lambda(m)$，$A_h(t)=\psi(t+h)-\psi(t)$，$e_h(t)=A_h(t)-h$。Selberg 在 RH 下的短区间均方估计，以及 RH 下的素数定理，给出 [1, 2]

$$
 \int_1^{2M}|e_h(t)|^2dt\ll M h L^2,\qquad
 |\psi(t)-t|\ll\sqrt M L^2\quad(M/6\le t\le 2M). \tag{3}
$$

给定 $a<u<b$，取 $T=(aM,uM]$。若 $m,r$ 是正整数，将同时满足 $t<m\le t+h$、$M-h-t<r\le M-t$ 的 $t$ 对实线积分，其长度恰为 $(h-|m+r-M|)_+$。这是两个长为 $h$、右端点分别为 $m$ 和 $M-r$ 的区间的重叠长度。归一化后，

$$
 \sum_{2\mid n}w_h(n-M)\nu_n((a,u])
 =\frac1{Mh^2}\int_T A_h(t)A_h(M-h-t)\,dt
   +O\!\left(\frac{h L^2+L^3}{M}\right). \tag{4}
$$

这里的误差对 $u$ 一致。为核对 (4)，先在所有 $n=m+r$ 上用 $1/M$ 代替 $1/n$。每个相关窗口有 $|n-M|<h$，对每个 $n$ 的未归一化总权至多 $O(M L^2)$，故代价为 $O(hL^2/M)$。将 $a<m/n\le u$ 换为 $t\in T$ 时，只有 $t$ 到 $aM$ 或 $uM$ 的距离为 $O(h)$ 才可能出错，因为 $|m-t|\le h$。每个短和均至多 $(h+1)L$（增大绝对常数即可），所以边界代价也是 $O(h L^2/M)$。偶数的非互素项必有 $m=p^k$、$p\mid n$，每个 $p$ 的总权至多 $L^2$，合计 $O(L^3)$。奇数的非零项至少有一个变量为二的幂，总权至多 $O(L^2)$。这就恢复了偶数与互素限制。

将两个 $A_h$ 写成 $h+e_h$。设 $E(t)=\psi(t)-t$，则对任意内部区间 $(A,B]$ 有

$$
 \int_A^B e_h(t)dt
 =\int_B^{B+h} E(t)dt-\int_A^{A+h}E(t)dt
 \ll h\sqrt M L^2.
$$

对反射后的区间同理，故两条线性误差在 (4) 归一化之后为 $O(L^2/\sqrt M)$。二次误差用 Cauchy–Schwarz 和 (3)，

$$
 \left|\int_T e_h(t)e_h(M-h-t)dt\right|\ll M h L^2.
$$

主项为 $|T|/M=u-a$。由于 $h\le\sqrt M$，各项合并给出

$$
 \sup_{u\in I}\left|\sum_{2\mid n} w_h(n-M)\nu_n((a,u])-(u-a)\right|
 \ll L^2/h. \tag{5}
$$



## 局部奇异级数与素数对的个数

<small>原稿第 3 页</small>

将 $S_n$ 在奇数上设为零。令 $C_2=\prod_{p>2}(1-(p-1)^{-2})$，在奇平方自由数上设置乘法权 $b(d)=\prod_{p\mid d}1/(p-2)$，其余 $d$ 的权为零。则

$$
 S_n=2C_2\,\mathbf1_{2\mid n}\sum_{d\mid n}b(d).
$$

$w_h$ 是两个长度 $h$ 的离散均匀区间取差得到的分布。固定一个位置，另一个位置在模 $k$ 的任一剩余类中出现 $h/k+O(1)$ 次，因此
$\sum_jw_h(j)\mathbf1_{k\mid M+j}=k^{-1}+O(h^{-1})$。又 $\sum_{d\le 2M}b(d)\ll L$ 由 Mertens 乘积给出，$\sum_{d>2M}b(d)/d\ll M^{-1/2}$ 由 $\sum b(d)/\sqrt d<\infty$ 得到。因 $C_2\sum b(d)/d=1$，可得

$$
 \sum_n w_h(n-M)S_n=1+O(L/h+M^{-1/2}),\qquad
 \sum_n w_h(n-M)S_n^2\ll 1+L^2/h. \tag{6}
$$

第二式同样展开，平方的局部权为 $b_2(p)=(1+1/(p-2))^2-1=2/p+O(p^{-2})$。于是 $\sum_d b_2(d)/d\ll1$ 且 $\sum_{d\le2M}b_2(d)\ll L^2$。由 (5)、(6) 与第 1 页的核估计得到 (1)。

**由局部平均推出多表示。** 在 $J$ 内取固定半开子区间，长度为 $\lambda>0$。用 (5) 在两个端点作差。记 $Q_n$ 为 $p/n\in J$ 的有序素数对的 $\log p\log q$ 权之和除以 $n$，在奇数上设为零。高次素数幂的总归一化权为 $O(L/\sqrt M)$，因为 $\sum_{p^k\le2M,k\ge2}\log p\ll\sqrt M$。因此取 $C_J$ 充分大就有 $\sum_n w_h Q_n\ge\lambda/2$。Selberg 上界筛给 $Q_n\ll S_n$。[3]

取足够小的 $\delta_J>0$，使 $Q_n<\delta_JS_n$ 的项由 (6) 至多贡献 $\lambda/4$。令 $G$ 为窗口内满足 $Q_n\ge\delta_JS_n$ 的偶数。由 (6)、$w_h\le 1/h$ 与 Cauchy–Schwarz，

$$
 \lambda/4\le \sum_{n\in G}w_h Q_n
 \ll \Big(\sum_n w_h S_n^2\Big)^{1/2}
       \Big(\sum_{n\in G}w_h\Big)^{1/2}
 \ll (|G|/h)^{1/2}.
$$

所以 $|G|\gg_J h$。每对的权至多 $(\log n)^2$，定理 2 随即成立。

**对固定比例缺陷的限制。** 若偶数 $M$ 有 $\|B_M\|\ge cS_M$，则 $D=\|\widetilde B_M\|\gg_c S_M$。取偶数 $h\ge C_c L^2$，$h\le\sqrt M$，偶数权重之和恰为 $1/2$。由 (1) 与三角不等式，$d_n=\|\widetilde B_M-\widetilde B_n\|$ 在偶数上的加权和至少为 $D/2-O(L^2/h)\ge D/4$。又 $\|\widetilde B_n\|\ll S_n$ 由总变差的上界筛估计得到，故 $\sum_{2\mid n}w_h d_n^2\ll D^2+1\ll_c D^2$。对 $d_n\ge D/4$ 的项用上式相同的 Cauchy–Schwarz 论证，有 $\gg_c h$ 个偶数满足 $d_n\gg_c S_M$。单个缺陷必须伴随短距离上的算子变化。



## 大筛和高阶矩要达到什么精度

<small>原稿第 4 页</small>

设 $X\le n\le2X$，$L_X=\log(2X)$，$e(x)=\exp(2\pi i x)$，$F_y(\alpha)=\sum_{m\le y}\Lambda(m)e(m\alpha)$，$y\le2X$。Farey 分数的间隔至少为 $Q^{-2}$，Montgomery–Vaughan 的加性大筛给出 [4]

$$
 \sum_{q\le Q}\sum_{a\bmod q}^{*}|F_y(a/q)|^2
 \ll (X+Q^2)\sum_{m\le y}\Lambda(m)^2
 \ll (X+Q^2) X L_X .
$$

在 $Q\asymp\sqrt X/L_X$ 处，右侧为 $O(X^2 L_X)$。这一界对一般系数成立。取长度为 $D$ 的系数 $a_m=e(-m\alpha_0)$，仅样本 $\alpha_0$ 一项就给出 $D^2$，而 $\sum|a_m|^2=D$。要控制指定 $n$ 的加法相关，还需用到素数系数的相位。

**把高阶矩放在正确的量上。** 令 $E_n(y)=\sum_{m+r=n,m\le y}\Lambda(m)\Lambda(r)-S_n\min(y,n)$，求和取正整数。前篇式 (7) 对 $I=(a,b)$ 给出
$\|B_n\|_{\rm HS}^2\ll n^{-3}\int_{an}^{bn}|E_n(y)|^2dy+L_X^6/n^2$。用 Hölder 不等式，对任意固定整数 $k\ge1$，

$$
 \sum_{\substack{X\le n\le2X\\2\mid n}}\|B_n\|_{\rm HS}^{2k}
 \ll_k X^{-2k-1}\int_0^{2X}
       \sum_{\substack{X\le n\le2X\\2\mid n}}|E_n(y)|^{2k}dy
       +X^{1-2k}L_X^{6k}. \tag{7}
$$

若 $H_y=F_yF_{2X}-J_yJ_{2X}$ 是圆法扣除模型的函数，准确的傅里叶恒等式为 $\sum_{n\in\mathbb Z}|\widehat H_y(n)|^{2k}=\|H_y^{*k}\|_{L^2(\mathbb T)}^2$，其中 $*$ 为圆上的卷积。直接估计 $\int|F_y|^{4k}$ 涉及另一组加法方程。模型傅里叶系数与奇异级数主项的误差为 $O_\varepsilon(X^{1/2+\varepsilon})$，在下面的目标尺度内可吸收。

**足以结束逐点问题的目标。** 设 $d_n=\|B_n\|/S_n$。若对给定 $k$ 能把截点矩一致地估到
$\sum_n |E_n(y)|^{2k}\ll_k X^{1+3k/2} L_X^{4k}$（此处及 (7) 的 $n$ 均为该区间内偶数），则

$$
 \sum_n d_n^{2k}\ll_k X^{1-k/2}L_X^{4k}. \tag{8}
$$

$k=1$ 是前篇已经达到的尺度。$k=2$ 将固定比例缺陷压到 $O_c(L_X^8)$ 个。$k=3$ 会给 $\max_n d_n\ll X^{-1/12}L_X^2$，足以对每个大偶数消去平衡压缩的缺陷。后两项是待证的算术矩估计。现有 $d_n\ll1$ 与二阶矩只能直接推出 $\sum d_n^{2k}\ll_k\sqrt X L_X^4$。短区间有符号平均 (1) 也没有提供 (8) 所要求的绝对矩。



## Frobenius 纤维与 Gowers 范数的检验

<small>原稿第 5 页</small>

**真实问题中可几何化的部分。** 对每个素数 $p$，考虑仿射直线上 $x(n-x)\ne0$ 的点。点数恰为 $p-2+\mathbf1_{p\mid n}$，因此其归一化密度

$$
 \frac{\#\{x\in\mathbb F_p:x(n-x)\ne0\}/p}{(1-1/p)^2}
 =\frac{p(p-2+\mathbf1_{p\mid n})}{(p-1)^2}
$$

正好给出 $S_n$ 在 $p$ 处的 Euler 因子。若要把整个 $T_n$ 解释为 Frobenius 作用，还须构造能恢复整数权 $\Lambda(m)\Lambda(n-m)$ 的对象，证明迹或矩阵元恒等式，并对每个参数控制导子及几何退化。局部密度计算只完成了主项的识别。

**一个只有单个坏纤维的族。** 取素数 $p\equiv3\pmod4$，$\chi$ 为二次特征，$\chi(0)=0$。任意指定 $t_0=2a$，令 $f(x)=\chi(x-a)$，
$C(t)=p^{-1}\sum_x f(x)f(t-x)$。对每个 $t\in\mathbb F_p$ 精确地有

$$
 \boxed{\quad C(t)=
 \begin{cases}-1+1/p,&t=t_0,\\[1mm]1/p,&t\ne t_0.\end{cases}\quad} \tag{9}
$$

平移后取 $a=0$。当 $t=0$，每个非零 $x$ 都给出 $\chi(-1)=-1$。当 $t\ne0$，换元 $x=tz$，再用 $y=z/(1-z)$ 将 $z\ne1$ 双射到 $y\ne-1$。因 $\chi(z(1-z))=\chi(y)$，求和给 $-\chi(-1)=1$。几何上，纤维 $y^2=x(t-x)$ 在 $t\ne0$ 时有 $p+1$ 个仿射点。$t=0$ 时退化为两条在代数闭包上共轭的直线，在 $\mathbb F_p$ 上只有原点。退化参数有一个，点数差达到 $p$。

取归一化傅里叶变换 $\widehat f(\xi)=p^{-1}\sum_x f(x)e(-\xi x/p)$。因 $C=f*f$ 为归一化卷积，(9) 给
$\widehat f(\xi)^2=-p^{-1}e(-\xi t_0/p)$（$\xi\ne0$），$\widehat f(0)=0$。每个非零频率的模都等于 $p^{-1/2}$，在 $t_0$ 做反演时，各项的相位完全相合。

**高阶一致性与指定反射。** 对任意固定 $s\ge2$，展开 $U^s$ 范数。若 $2^s$ 个移位 $\omega\cdot h$ 两两相异，内层是平方自由多项式的二次特征和，Weil 界至多 $(2^s-1)\sqrt p$。碰撞的 $h\in\mathbb F_p^s$ 落在至多 $\binom{2^s}{2}$ 个超平面上。故 [5]

$$
 \|f\|_{U^s}^{2^s}\le (2^s-1)p^{-1/2}+\binom{2^s}{2}/p\longrightarrow0.
$$

然而 $A=a+\{x\ne0:\chi(x)=1\}$ 的密度为 $(p-1)/(2p)$，且 $t_0\notin A+A$。对 $t\ne t_0$，将平方剩余指示函数写成 $(\mathbf1_{x\ne0}+\chi(x))/2$，可得 $4r_A(t)=p-1-2\chi(t-t_0)$，其中 $r_A(t)$ 为有序表示数。故 $p\ge7$ 时恰好只漏一个和。对每个 $k\ge1$，$p^{-1}\sum_t|C(t)|^{2k}=p^{-1}(1-1/p)^{2k}+(1-1/p)p^{-2k}$，趋零的矩容得下这个异常。Green–Tao 的线性型理论也明确区分这类仿射相关的二元系统 [6]。这是对推理方式的检验，例子里的权是有限域二次特征。



## 谱统计、指标和算法信息

<small>原稿第 6 页</small>

**随机矩阵与 QUE。** 缺少指定区间的素数对，会在混合型中给出一个大范数方向。$\|B_n\|$ 由谱端决定。把 $d\times d$ 的 Hermitian 矩阵在其最大特征值的方向上加一个正的秩一扰动，其余 $d-1$ 个特征值及一整组特征向量均可保持原样，经验分布函数的变化至多 $1/d$。所以体谱间距统计允许单个远离体谱的特征值。量子唯一遍历约束特征态在可观测量上的分布，仍需额外的谱端估计来控制范数。Katz–Sarnak 的等分布定理以具体几何族及其单值群为输入 [7]。若能对真实整数族给出小于一个样本所占质量的尾界，才可依整数计数排空固定比例例外。

**非交换几何与指标。** 即使已有谱迹公式，Fredholm 指标为零也允许任意大的算子扰动。令 $P$ 为一个正交秩一投影，$I+tP$ 对每个 $t\ge0$ 可逆，从 $I$ 到 $I+tP$ 的路径全在可逆元中，指标恒为零，而 $\|(I+tP)-I\|=t$。在非交换环面代数里，标量路径 $(1+t)1$ 同样位于可逆元的单位连通分支。因而若用指标排除真实缺陷，需先证该缺陷会使某个具体 Fredholm 算子产生非零指标。Connes 的迹公式提供了谱解释的参照，未给出这里所需的对应 [8]。

**信息论确有一个可证明的推论。** 取端点为有理数的固定 $J\Subset I$。令 $E_k$ 为 $[2^k,2^{k+1})$ 中完全没有 $p/n\in J$ 的素数表示的偶数。给定 $k$，用有限次素性检验即可列完 $E_k$。这个判定只涉及素数表示。在它非空时，给出元素在列表中的序号，就能描述任何 $n\in E_k$。在固定通用前缀机上，列表长度可由 $k$ 算出，序号只占 $\lceil\log_2|E_k|\rceil$ 位。代入前篇的例外集估计，

$$
 K(n\mid k)\le \tfrac12 k+4\log_2 k+O_J(1)\qquad(n\in E_k). \tag{10}
$$

因此，给定尺度仍具有更高条件复杂度的偶数必有这种表示。若列表非空，其中第一个元素仅需固定长度程序描述。要从信息论产生矛盾，需要额外证明同一元素有更大的复杂度下界。Lovász 局部引理还需指定概率空间、坏事件和依赖关系，由此推出的正概率存在性也要再连回指定的整数。

### 文献与核验

[1] D. A. Goldston，*Linnik’s theorem on Goldbach numbers in short intervals*，[原文](https://doi.org/10.1017/S001708950000937X)。[2] A. Languasco、A. Perelli，*On Linnik’s theorem on Goldbach numbers in short intervals and related problems*，[式 (1)](https://www.numdam.org/item/AIF_1994__44_2_307_0/)。[3] R. C. Vaughan，*The Selberg Sieve*，[例 5](https://personal.science.psu.edu/rcv4/571s25/Class571-04.pdf)。[4] H. L. Montgomery、R. C. Vaughan，*Multiplicative Number Theory II*，[推论 19.5](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf)。  
[5] L. Babai 等，[定理 3.7 所述 Weil 特征和界](https://people.cs.uchicago.edu/~laci/papers/span1.pdf)。[6] B. Green、T. Tao，*Linear equations in primes*，[Annals](https://annals.math.princeton.edu/2010/171-3/p08)。[7] N. Katz、P. Sarnak，*Random Matrices, Frobenius Eigenvalues, and Monodromy*，[AMS](https://doi.org/10.1090/coll/045)。[8] A. Connes，*Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*，[作者书目](https://alainconnes.org/publications/)。

Lean 4.19.0 核验了 12 条引理，涉及区间重叠、线性项的端点公式、二次项的积分界、六阶矩转移、由权重推出个数、算子变化量、矩对单项的控制，以及有限域的局部点数、反射相关、缺失和、傅里叶相位及全部偶矩。式 (1)、(2) 的完整证明和一般的 Weil 界仍采用解析论证与所引文献。
