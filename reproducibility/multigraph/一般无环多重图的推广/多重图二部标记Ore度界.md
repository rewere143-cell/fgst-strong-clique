# 二部标记强团的多重图 Ore 度上界

**定理。** 若 \(G\) 是有限无环多重图，\(H\) 是边集构成强团的二部子多重图，且

\[
\sigma=\max_{xy\in E(H)}(d_G(x)+d_G(y)),
\]

则 \(e(H)\le (620/1987)\sigma^2\)。宿主 \(G\) 可以含三角形，度数与边数都按平行边的份数计算。证明使用整数区间核验。

本证明调整了 Kumar–Mohar–Pragada 对简单图的二部标记计数。额外保留根的不同邻点数、标记重度及余部覆盖界，因此允许任意平行重数。[Kumar–Mohar–Pragada，第 2 节](https://arxiv.org/html/2607.02698v1#S2)

## 归约到三个标量

令 \(\beta=620/1987\)。按标记边实例数 \(m=e(H)\) 归纳。空强团或单边强团直接成立。取一个标记度最大的点 \(v\)，记 \(D=\Delta(H)\)。令 \(X\cup Y\) 为 \(H\) 的二部划分，可设 \(v\in X\)。以下用

\[
a=D/\sigma,\qquad p=|N_H(v)|/\sigma,\qquad
b=\max_{z\in N_H(v)}d_H(z)/\sigma,\qquad r=d_G(v)/\sigma .
\]

于是 \(p\le a\)、\(b\le a\)、\(a+b\le1\)、\(r+b\le1\)。记 \(M=m/\sigma^2\)。

先取 \(v\) 的一个标记度等于 \(b\sigma\) 的标记邻点 \(y\)，令 \(q=|N_H(y)|/\sigma\)。除 \(vy\) 束外的标记边都接触 \(R=(N_G(v)\cup N_G(y))\setminus\{v,y\}\)。其中 \(p\sigma-1\) 个点的标记度至多 \(b\sigma\)，其余点的标记度至多 \(D\)。两根宿主度之和至多 \(\sigma\)，其中至少有 \((a-p+b-q)\sigma\) 份超过不同邻点数。计入 \(vy\) 束的标记重数 \(w\le b\sigma\)，得到

\[
\begin{aligned}
M
&\le a(1-a-b+q)+pb+(w-b\sigma-D)/\sigma^2\\
&\le a(1-a)+pb .
\end{aligned}
\tag{1}
\]

再设 \(A=N_H(v)\)、\(C=N_G(v)\setminus A\)、\(B=V(G)\setminus N_G[v]\)，令 \(F=H[B]\)、\(f=e(F)/\sigma^2\)。记 \(\Pi\) 为 \(A,B\) 之间未标记的宿主边实例数。由于 \(A\subseteq Y\)，每条标记边在 \(A\) 中至多有一个端点。又因 \(d_G(z)\le(1-r)\sigma\) 对每个 \(z\in A\) 成立，接触 \(A\) 的标记边总数至多 \(p(1-r)\sigma^2-\Pi\)。由于 \(v\) 的 \(D\) 份标记边已经消耗 \(D\) 份根度，\(|C|\le(r-a)\sigma\)，故接触 \(C\) 的标记边数至多 \(a(r-a)\sigma^2\)。除 \(F\) 外，每条标记边接触 \(A\cup C\)。于是

\[
M\le a(1-a)-(a-p)(1-r)+f-\Pi/\sigma^2 .
\tag{2}
\]

每条 \(xy\in E(F)\) 与每条 \(vz\)（\(z\in A\)）必须相强，但 \(x,y\notin N_G[v]\)。因此每个 \(z\in A\) 都邻接 \(x,y\) 之一。这有两个后果。

- 对任意 \(z\in A\)，集合 \(N_G(z)\cap B\) 覆盖 \(E(F)\)。沿此覆盖求和标记度得到 \(f\le a(1-r)\)。
- \(F\) 在 \(G[B]\) 内继续构成强团，且每个 \(F\) 边束的两端总共失去至少 \(p\sigma\) 份宿主度。由于 \(F\) 比 \(H\) 少至少一份标记边，归纳给出 \(f\le\beta(1-p)^2\)。

令 \(h_x\) 表示 \(x\in X\cap B\) 至 \(A\) 的标记边实例数，\(f_x=d_F(x)\)。对每个 \(F\) 边实例，把 \(|A|\) 个不同的见证邻接逐一计入未标记的 \(A,B\) 边或标记的 \(A,X\cap B\) 边，再求和。未标记边 \(uz\) 的贡献至多 \(d_F(u)\le D\)，其中 \(u\in B,z\in A\)。标记边的贡献位于 \(X\cap B\)，故

\[
|A|e(F)\le D\Pi+\sum_{x\in X\cap B}h_x f_x .
\]

因为 \(h_x+f_x\le D\)，可用

\[
\frac{1}{D}\sum_x h_x f_x
\le \sum_x\frac{h_x f_x}{h_x+f_x}
\le\frac{(\sum_x h_x)(\sum_x f_x)}{\sum_x h_x+\sum_x f_x}.
\]

约定 \(0/0=0\)。后一不等式来自 Cauchy–Schwarz，或把每项上界成 \(\theta^2 h_x+(1-\theta)^2 f_x\) 再对 \(\theta\) 最小化。每个 \(A\) 点的标记度至多 \(b\sigma\)，所以 \(\sum h_x\le pb\sigma^2\)。又有 \(\sum f_x=e(F)\)，于是

\[
\Pi/\sigma^2\ge (p/a)f-\frac{pb f}{pb+f}.
\]

将此式代入 (2)，再用 \(1-r\ge\max(b,f/a)\)，得

\[
M\le a(1-a)-(a-p)\max(0,b-f/a)+\frac{pb f}{pb+f}.
\tag{3}
\]

式 (3) 的右侧随 \(f\) 非减，故可把 \(f\) 换成 \(f_*=\beta(1-p)^2\)。

## 整数区间核验

对所有 \(0<a\le1\)、\(0\le p\le a\)、\(0\le b\le\min(a,1-a)\)，式 (1) 和把 \(f\) 换成 \(f_*\) 的式 (3) 至少一个至多 \(\beta\)。[整数复验脚本](check_multigraph_bipartite_ore.py)

脚本对 \((a,p,b)\) 的可行区域作二分。用 \(A_*\) 表示盒内 \(a(1-a)\) 的最大值，\(k_*=p_1b_1\)、\(g_*=\beta(1-p_0)^2\)。两项的逐盒上界为

\[
A_*+k_*,\qquad
A_*-(a_0-p_1)_+\bigl(b_0-g_*/a_0\bigr)_+
+\frac{k_*g_*}{k_*+g_*}.
\]

这里 \(a_0=0\) 时减项按零计，下标 \(0,1\) 分别为区间下、上端。判定上界是否至多 \(\beta\) 时清分母，只用整数。若两个上界都未能核验，二分最长坐标。运行复验脚本，使用整数尺度 \(2^{34}\)，得到 54,608 次分割，最大深度 56，无未决盒。因此 (1)、(3) 给出 \(M\le\beta\)，完成归纳。
