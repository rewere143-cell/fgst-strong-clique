# 二部标记强团的递推 Ore 上界

设 \(G\) 为有限无环多重图，标记强团 \(H\) 的标记图为二部图。按实例计度数，定义 \(\sigma=\max_{xy\in E(H)}(d_G(x)+d_G(y))\)。则
\[
e(H)\le \frac{1489}{5000}\,\sigma^2=.2978\,\sigma^2.
\]
宿主可以有三角形。该估计更新本阶段原有的 \(.2989\,\sigma^2\) 上界。

沿用[原两级计数](多重图两级余量计数.md)的记号。\(a=\Delta(H)/\sigma\)，\(p=a\theta\) 为最大标记度根的不同标记邻点数比，\(a\mu\) 为该根闭邻域外剩余标记最大度比。接触标记邻域的标记边数比 \(T\) 至多 \(p\min(a,1-a)\)。闭邻域外标记边数比 \(f\)，可按 \(\tau\sigma=(1-p)\sigma\) 归一化。在这个归一化中，其最大标记度比在 \(a\mu/\tau\)。若某个分段常数函数 \(U\) 给所有二部标记强团的条件上界，则本次根的 \(f\) 上界为
\[
f\le \min\bigl(\tau^2 U(a\mu/\tau),\,a\mu(1-a)\bigr).
\]
第二项来自每个根标记邻点对剩余标记边的点覆盖计数，及根宿主度至少为 \(a\sigma\)。

对应原计数式 (2)、(5)、(6)，只需核验
\[
\frac{e(H)}{\sigma^2}\le a(1-a)+
\min\left\{
T_{\max},\
\max_{0\le T\le T_{\max}}\left[T-\frac{T^2}{\theta(T+f_{\max})}\right],\
\max_{\substack{0\le T\le T_{\max}\\0\le f\le f_{\max}}}
\frac{Tf/(T+f)-\mu(1-\theta)T-\theta(1-\mu)f}{\theta\mu}
\right\}.
\]
当 \(\theta+\mu\le1\) 时已有 \(e(H)/\sigma^2\le a(1-a)\)。\(a(\theta+\mu)>1\) 与剩余 Ore 界冲突。其余盒子按原计数用参数上端界住两个最大值，取子区间相交的全部表项最大值界住 \(U(a\mu/\tau)\)。

初始表使用旧 \(.2989\) 定理及 \(\mu=1\) 时的一层计数，512 个 \(a\) 区间逐个有理计算。然后连续三次使用上式，每次将参数 \(a\) 划成 192 个等宽闭区间。对于候选表的每个条目，若旧表已给更小上界则沿用旧表；否则在 \((a,\theta,\mu)\) 中作精确有理区间验证。最后再对整个参数范围使用第三张表。候选数值只用来提出要核验的有理上界。每个被采用的条目均由同一有理核验器证明。

[固定候选表](multigraph_recursive_ore_candidates.json)三次各验过 178、148、148 个需要改进的条目，无未决条目。最终 14,812 次二分、最大深度 34 后所有盒子均通过。[精确再验报告](multigraph_recursive_ore_2978.json)

~~~text
python -B check_multigraph_recursive_ore.py --suggestions multigraph_recursive_ore_candidates.json --target 1489/5000 --limit 1400
~~~
