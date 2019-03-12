<h2 id="section-general-linear-group" class="tex-section"><span data-tag="0005">4</span> The general linear group</h2>

<p>
The most important example of an affine algebraic group for us is $GL(n)$ over $K$. Let $R=K[x_0,x_{ij}:i=1,\ldots ,n;j=1,\ldots ,n]$ be a polynomial ring in $n^2+1$ variables $x_0$ and $x_{ij}$. Let $\det (x_{ij})\in R$ be the determinant in $x_{ij}$. Define $GL(n)$ as an affine variety by its coordinate ring: $K[GL(n)] = R/(x_0\det (x_{ij}) - 1)$. We set $y_{ij} = x_{ij}\otimes 1$ and $z_{ij} = 1\otimes x_{ij}$ in $K[GL(n)\times GL(n)]$. Then 
</p>
<div class="equation">
  \[  K[GL(n)]\otimes K[GL(n)] \simeq K[y_0,y_{ij},z_0,z_{ij}]/(y_0 \det (y_{ij})-1,z_0\det (z_{ij})-1).  \]
</div>
<p>
There exists a unique affine algebraic group $GL(n)$ with coordinate ring $K[GL(n)]$ and 
</p>
<div class="equation">
  \begin{align*}  e^*(x_{ij}) & = \delta _{ij} \text{ (Dirac delta function)},& e^*(x_0) & = 1\\  \mu ^*(x_{ij}) & = \sum _{i=1}^ n {y_{ik} z_{kj}},& \mu ^*(x_0) & = y_0 z_0\\  i^* & = \text{adjugate formula for matrix inverse},& i^*(x_0)& =\det (x_{ij}). \end{align*}
</div>
<p>
 The adjugate formula appears here <span class="cite">[<a href="/bibliography/WA">WA</a>]</span>. 
</p>
<p>
If $a \in GL(n)(K) = GL(n,K) = \text{Hom}_{K-alg}(K[GL(n)],K)$, we write $a_{ij}$ for $a(x_{ij})\in K$, and write it as an $n\times n$ matrix with coefficients in $K$. If $a_0 = a(x_0)$, then $a_0\det (a_{ij})=1$, so that the determinant of the matrix is nonzero. In fact, the element $x_0$ appears exactly for the purpose of expressing the non-zero determinant condition as a polynomial equation. 
</p>
