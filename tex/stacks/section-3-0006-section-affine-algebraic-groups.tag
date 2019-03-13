<h2 id="section-affine-algebraic-groups" class="tex-section"><span data-tag="0006">3</span> Affine algebraic groups</h2>

<p>
Henceforth we refer to a group in the usual sense as abstract groups to distinguish them from <em>affine groups</em>, which are group objects in the category of affine categories, which are described in this section. 
</p>
<p>
We fix an algebraically closed field $K$. The objects from the categories of affine varieties and affine groups are all over this field $K$. 
</p>
<p>
An affine group over $K$ is defined as an affine variety $G$, together with morphisms $\mu :G \times G \to G$ (called multiplication) $i:G \to G$ (called inverse), and $e:1\to G$ (identity element) such that $\mu $ and $i$ satisfy the usual axioms of a group. More precisely, we mean the axioms of a group in the category of affine algebraic groups. For example, the right inverse property is that this diagram commutes: The other axioms are obtained by a similar translation of the group axioms into categorical language. The axioms are written explicitly in the Wiki article on group object <span class="cite">[<a href="/bibliography/group-object">group-object</a>]</span>. (These axioms can also be expressed directly in $A_ K$ as the axioms of a Hopf algebra.) 
</p>
<p>
If $G$ is an affine group, then the corresponding operations on the spectrum 
</p>
<div class="equation">
  \[  \mu _*:G(K)\times G(K)\to G(K),\quad e_*(1)\in G(K),\quad i_*:G(K)\to G(K)  \]
</div>
<p>
 make $G(K)$ into a group. 
</p>
<p>
A morphism $f:G\to G'$ of affine algebraic groups is a morphism of affine varieties such that $f(x y) = f(x) f(y)$. That is, this diagram commutes: Unless stated otherwise, a morphism will mean a group homomorphism of affine algebraic groups. 
</p>
<p>
The point $1$ has the structure of an affine group. 
</p>
<p>
If $G$ and $G'$ are affine groups, then $G \times G'$ also carries the structure of an affine group in a natural way. 
</p>
<p>
A closed subgroup $H$ of an affine group $G$ is a closed subvariety that contains the neutral element and such that the inverse and multiplication on $G$ restrict to $H$. Then $H$ has the structure of an affine group. In what follows, being <em>closed</em> refers to the Zariski topology, but never to the algebraic sense in which a binary operation can be closed. 
</p>
<p>
The kernel of a morphism $\psi :G\to H$ is the closed subset given by the preimage of $1\in H$. The kernel of a morphism $\psi :G\to H$ is a closed subgroup of $G$. We define a normal subgroup of $G$ to be any closed subgroup obtained as a kernel of a morphism. 
</p>
<p>
An abelian group is an affine group such that 
</p>
<div class="equation">
  \[  G \times G \to G \times G \to ^\mu G  \]
</div>
<p>
 coincides with $\mu $, where the first morphism swaps the factors. 
</p>
<p>
A solvable group $G$ is defined inductively as an affine group that is abelian, or as an affine group $G$ that admits a morphism $\psi :G\to H$, where both $H$ and the kernel of $\psi $ are solvable. 
</p>
<p>
An affine group $G$ is connected, if it is connected as a topological space. A Borel subgroup of $G$ is a maximal closed connected solvable subgroup of $G$. 
</p>
<p>
Let $G$ be an affine group. There exists an abelian affine group $A$ (the abelianization of $G$) and morphism $G\to A$ with the following universal property: if $A'$ is any affine abelian group, and morphism $\psi : G \to A'$, there exists a unique $A\to A'$ such that $\psi $ is equal to $G\to A \to A'$. The kernel of $\phi :G\to A$ is the <em>closed derived</em> subgroup of $G$. The kernel does not depend on the choice of $(A,\phi )$. 
</p>
<p>
Let $G$ be an affine group and let $H$ be a subgroup of $G$. A closed subgroup $C$ of $G$ <em>centralizes</em> $H$ if the morphism of varieties 
</p>
<div class="equation">
  \[  C \times H \to G, \quad (c,h)\to c h c^{-1}  \]
</div>
<p>
 coincides with the inclusion $H\to G$. Among all closed subgroups $C$ centralizing $G$, there exists a unique maximal element (under the ordering by inclusion of closed subsets of $G$). This is the centralizer $C_ G(H)$ of $H$ in $G$. The center $Z = Z_ G$ of $G$ is the centralizer in $G$ of $G$: 
</p>
<div class="equation">
  \[  Z = C_ G(G).  \]
</div>
<p>
We say that a closed subgroup $N$ of $G$ normalizes another closed subgroup $H$ if the image of the morphism of varieties 
</p>
<div class="equation">
  \[  N \times H \to G,\quad (n,h) \mapsto n h n^{-1}  \]
</div>
<p>
 lies in $H$. When $N$ normalizes $H$, there is an action of $N$ on $H$ given by $(n,h) \mapsto n h n^{-1}$. 
</p>
