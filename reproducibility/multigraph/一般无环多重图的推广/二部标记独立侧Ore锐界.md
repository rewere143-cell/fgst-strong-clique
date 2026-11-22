# 二部标记强团在独立侧条件下的锐 Ore 度界

设 \(G\) 是有限无环多重图，\(H\) 是边集构成强团的二部子多重图，二部侧记为 \(X,Y\)。假设 \(Y\) 在宿主 \(G\) 中也独立，并且 \(H\) 的最大标记度 \(D\) 在 \(X\) 中取得。令 \(\sigma=\max_{uv\in E(H)}(d_G(u)+d_G(v))\)。则

\[
e(H)\le D(\sigma-D)\le \sigma^2/4.
\]

完全二部图取所有边为标记边时，第一项上界达到。两部同样大小时第二项也达到。证明允许任意平行重数。

取 \(x\in X\) 有 \(d_H(x)=D>0\)。记 \(A=N_H(x)\)、\(p=|A|\)、\(C=(N_G(x)\cap Y)\setminus A\) 和 \(S=N_G(x)\cap X\)。度数计重数，集合只数不同点。因此

\[
|S|+|C|\le d_G(x)-D,\qquad p\le D.
\]

令 \(T\subseteq X\setminus(S\cup\{x\})\) 是有标记邻点落在 \(Y\setminus N_G(x)\) 的顶点集。任意 \(t\in T\) 取这样的标记邻点 \(y\)。对每个 \(z\in A\)，边 \(ty\) 必须与 \(xz\) 相强。四个端点不同，\(xt,xy\) 都不存在，\(zy\) 因 \(Y\) 独立也不存在。因此 \(tz\) 必须存在。这证明 \(A\) 与 \(T\) 之间的宿主邻接完整。又对每个 \(z\in A\)，标记边 \(xz\) 给出 \(d_G(z)\le \sigma-d_G(x)\)。于是

\[
|T|\le \sigma-d_G(x),\qquad
e_H(A,X\setminus T)\le p(\sigma-d_G(x)-|T|).
\]

每条标记边或接触 \(S\cup C\)，或接触 \(T\)，或从 \(A\) 到 \(X\setminus T\)。沿这些集合求上界得

\[
\begin{aligned}
e(H)
&\le D(|S|+|C|)+D|T|+p(\sigma-d_G(x)-|T|)\\
&\le D(d_G(x)-D)+p(\sigma-d_G(x))+(D-p)|T|\\
&\le D(\sigma-D).
\end{aligned}
\]

事实上，只需在上述根 \(x\) 处没有宿主边连接 \(A\) 和 \(Y\setminus N_G(x)\)。因此这一局部无边条件足以代替全侧独立。若单独记两侧的最大标记度 \(D_X,D_Y\)，选 \(d_H(x)=D_X\)，同一计数仍给出

\[
e(H)\le D_X(\sigma-D_X)+(D_Y-D_X)_+|C|.
\]

特别地，若有一条标记边同时连接两侧各自的最大标记度点，则仍有 \(e(H)\le\sigma^2/4\)。当 \(D_Y>D_X\) 时，选该边的 \(X\) 端点作为 \(x\)，则 \(|C|\le \sigma-D_X-D_Y\)。令 \(u=D_Y-D_X\)、\(v=\sigma-D_X-D_Y\)，均非负。附加量至多 \(uv\le (u+v)^2/4=(\sigma/2-D_X)^2\)，恰可用 \(D_X(\sigma-D_X)\) 与 \(\sigma^2/4\) 的差抵消。
