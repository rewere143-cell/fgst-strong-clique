# 二部剩余图的匹配型 Ore 判据

设 \(H\) 的边实例构成有限无环多重宿主 \(G\) 上的强团，且标记图二部，二部侧为 \(X,Y\)。记最大标记度为 \(a\)，标记端点 Ore 度为 \(\sigma\)。选最大标记度根 \(v\in X\)，令 \(d=d_G(v)\)，
\[
 A=N_H(v),\quad p=|A|,\quad C=N_G(v)\setminus A,\quad
 B=V(G)\setminus N_G[v],\quad H_0=H[B].
\]
令 \(T\subseteq X\cap B\) 为 \(H_0\) 中非孤立的点集。对 \(u\in A\)，记
\[
 T_u=T\setminus N_G(u),\qquad Y_u=N_{H_0}(T_u),\qquad
 \delta=\sum_{u\in A}(|T_u|-|Y_u|).
\]
则
\[
 m\le a(\sigma-a)+\frac a p\delta .
\tag{1}
\]
特别是 \(\delta\le0\) 时，\(m\le a(\sigma-a)\le\sigma^2/4\)。若 \(H_0\) 的简单支撑有匹配覆盖整个 \(T\)，或较弱地对实际选的每个 \(T_u\) 有 \(|Y_u|\ge|T_u|\)，即满足这个条件。这里不要求任一侧在宿主中独立。

## 证明

对 \(u\in A\) 与 \(y\in Y_u\)，存在 \(x\in T_u\) 使 \(xy\) 标记。比较标记 \(vu,xy\)，两端 \(x,y\) 不见根 \(v\)，且 \(x\) 不见 \(u\)，所以 \(y\) 见 \(u\)。\(Y_u\) 与 \(u\) 同属于标记二部侧 \(Y\)，故这些邻接全未标记。不同的 \(u\) 所要求的未标记边按其 \(A\) 端点分别计数，不重复。由此 \(u\) 的宿主度至少有
\[
 |T|-|T_u|+|Y_u|
\]
份已用在 \(T\) 或 \(Y_u\)。而 \(u\) 的宿主度至多 \(\sigma-d\)，合计得到
\[
 p|T|-\delta\le p(\sigma-d).
\]

所有标记边或接触 \(C\)，或接触 \(T\)，或接触 \(A\)。在最后一项只数不接触 \(T\) 的标记，既可扣掉已使用的 \(A,T\) 间宿主度，也可扣掉上述同侧未标记边。因 \(|C|\le d-a\)，得到
\[
 m\le a(d-a)+a|T|+p(\sigma-d)-p|T|+\delta.
\]
用 \(a-p\ge0\) 代入 \(|T|\le\sigma-d+\delta/p\)，即得到 (1)。

## 标记度加权的版本

还可任取权 \(w_x\in[0,1]\)，使
\[
 d_{H_0}(x)\le w_x(a-d_H(x,A))\qquad (x\in T).
\tag{2}
\]
例如取 \(w_x=d_{H_0}(x)/(a-d_H(x,A))\)，分母为零时取零；此时 \(d_{H_0}(x)=0\)，不会有 \(x\in T\)。仍令 \(Y_u\) 为 \(H_0\) 中 \(T_u\) 的另一侧邻集，定义
\[
 \delta_w=\sum_{u\in A}\left(\sum_{x\in T_u}w_x-|Y_u|\right).
\]
则
\[
 m\le a(\sigma-a)+\frac a p\delta_w.
\tag{3}
\]
确实，(2) 允许对 \(H_0\) 每个 \(X\) 端点计 \(a w_x\)，并从 \(A\) 汇总的标记度扣除 \(w_x d_H(x,A)\)。因此在宿主总度中可以扣除 \(w_x|N_G(x)\cap A|\)，因为其余蓝容量已在标记度损失中。另扣的 \(A,Y_u\) 蓝边与这些项不交。线性比较与 (1) 相同，只需把 \(|T|\) 换成 \(\sum_xw_x\)，把 \(\delta\) 换成 \(\delta_w\)。

这说明二部标记 Ore 界如果失败，则每个最大标记度根的剩余图都存在跨侧扩张亏损，带权版本必须满足
\[
 \delta_w>\frac p a(a-\sigma/2)^2 .
\]
这仍是一项局部归约。一般二部标记图是否总能找到使 \(\delta_w\le0\) 的适用根，未由此证明。


## 同侧见证的平方根亏损

沿用以上最大标记度根 \(v\in X\) 的记号。令 \(E\) 为 \(A\) 和 \(Y\cap B\) 间的不同宿主端点对数，这些端点对全部蓝色。则
\[
 m\le a(\sigma-a)+2\sqrt{a(\sigma-d)E}
     \le \sigma^2/4+\sigma\sqrt E .
 \tag{4}
\]
因此可以用标记二部任一对图中，最大标记度根的对侧内部全部宿主端点对数来上界 \(E\)。若最大标记度根出现在两侧，则可以择有较少对侧内部宿主边的根。

取 \(0<\theta<1\)，暂时只取消所有如下标记实例的标记资格，不改变宿主。被取消的实例落在 \(H_0\)，且其 \(X\) 端点 \(x\) 满足 \(d_H(x,A)>(1-\theta)a\)。由于
\[
 \sum_{x\in X\cap B}d_H(x,A)\le p(\sigma-d),
\]
这样的 \(x\) 至多有 \(p(\sigma-d)/[(1-\theta)a]\) 个，每个接触被取消的实例至多有 \(\theta a\) 份。总损失至多 \(p(\sigma-d)\theta/(1-\theta)\)。所有 \(A\) 的红邻接以及根的最大标记度 \(a\) 都原样保留。

对剩余标记使用 (3)。每个 \(x\in T\) 取
\[
 w_x=\frac{d_{H_0}(x)}{a-d_H(x,A)}\le
 \frac{d_{H_0}(x)}{\theta a}.
\]
现在 \(H_0\) 及集合 \(T,T_u,Y_u\) 均按取消若干标记后的图计算。令 \(E'=\sum_u|Y_u|\le E\)。定义 \(g_y=|\{u\in A:y\in Y_u\}|\)。每条剩余标记边 \(xy\in H_0\) 满足 \(p-|N_G(x)\cap A|\le g_y\)，因为 \(x\) 所遗漏的每个 \(u\in A\) 都把 \(y\) 加入 \(Y_u\)。所以
\[
 \sum_{x\in T}w_x(p-|N_G(x)\cap A|)
 \le \frac{1}{\theta a}\sum_{xy\in E(H_0)}g_y
 \le \frac1\theta\sum_y g_y
 =E'/\theta.
\]
这里首个求和按剩余标记实例，且 \(d_{H_0}(y)\le a\)。代入 \(\delta_w\le E'(1/\theta-1)\) 和删除损失，得到
\[
 m\le a(\sigma-a)+p(\sigma-d)\frac{\theta}{1-\theta}
       +\frac{aE}{p}\frac{1-\theta}{\theta}.
\]
对正实数 \(\theta/(1-\theta)\) 极小化，得到 (4) 的首个上界。若某系数为零则取极限，结论相同。再用 \(d\ge a\) 和 \(a(\sigma-a)\le\sigma^2/4\) 即得第二个上界。