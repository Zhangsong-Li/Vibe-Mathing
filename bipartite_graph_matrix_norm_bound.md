# lemma lem:same-side-edges-and-cover-exponent

## statement
Let \(\alpha\) be a fixed graph whose vertices are partitioned as
\[
V(\alpha)=U_\alpha\sqcup W_\alpha .
\]
Let \(H_\alpha\) be the bipartite graph with vertex classes \(U_\alpha,W_\alpha\) and edge set consisting only of the edges of \(\alpha\) with one endpoint in \(U_\alpha\) and one endpoint in \(W_\alpha\).  Let
\[
\tau(\alpha)=\min\{|S|:S\subseteq V(H_\alpha)\text{ is a vertex cover of }H_\alpha\}.
\]
Then edges of \(\alpha\) lying entirely inside \(U_\alpha\) or entirely inside \(W_\alpha\) do not change \(\|M_\alpha\|\).  Consequently it is enough to prove norm estimates for the bipartite cross-edge graph \(H_\alpha\).

## proof
For a realization \(\varphi\), the product over same-side edges in \(U_\alpha\) depends only on the row index \(\varphi(U_\alpha)\).  Thus those factors multiply rows by signs.  Similarly, the product over same-side edges in \(W_\alpha\) depends only on the column index and multiplies columns by signs.  Multiplication on the left or right by a diagonal sign matrix is an isometry for the operator norm.  Therefore the operator norm is unchanged after deleting all same-side edges.

For a bipartite graph, a set meeting every cross edge is exactly a vertex separator between the left and right sides in the sense that deleting it removes all left-right paths.  Thus in this two-sided setting the minimum separator size is the minimum vertex-cover size \(\tau(\alpha)\).

# lemma lem:even-bipartite-walk-count

## statement
Let \(X\) and \(Y\) be finite sets with \(|X|,|Y|\le C_0 n\).  Let \(N_k(X,Y)\) be the number of closed alternating walks
\[
y_1,x_1,y_2,x_2,\ldots,y_k,x_k,y_1,
\qquad x_i\in X,\quad y_i\in Y,
\]
such that every edge of the complete bipartite graph \(X\times Y\) traversed by the walk is traversed at least twice.  Then
\[
N_k(X,Y)\le C^k n^{k+1},
\]
whenever \(k^{C_*}\le n\), where \(C\) and \(C_*\) depend only on \(C_0\).  In particular this holds for \(k=\lceil\log n\rceil\) and all sufficiently large \(n\).

## proof
For such a walk \(P\), let \(\Gamma(P)\) be its support graph, with \(q\) distinct vertices and \(e\) distinct edges.  The support graph is connected, each of its edges is traversed at least twice, and the walk has length \(2k\).  Hence \(e\le k\) and \(q\le e+1\).  Put
\[
\delta=k+1-q .
\]
This is the vertex deficit from the tree-like case.

We need the following standard Füredi--Komlós encoding estimate.  The number of canonical equality patterns of such walks with exactly \(q=k+1-\delta\) support vertices is at most
\[
C_1^k k^{C_1\delta}. \tag{1}
\]
Here "canonical" means that vertices on each side are named by their order of first appearance, so that a canonical pattern records only which positions of the walk have equal labels.  For completeness we recall the encoding.  Expose the walk from its root \(y_1\).  First entrances into new vertices form a rooted plane tree.  If \(r=e-q+1\) is the graph excess and \(s=k-e\) is the multiplicity surplus, then
\[
\delta=(k-e)+(e-q+1)=s+r .
\]
Mark as exceptional the \(2s\) surplus traversals beyond the first two traversals of each support edge, and also the two mandatory traversals of each of the \(r\) non-tree support edges.  After deleting these exceptional traversals, the remaining walk traverses each edge of a rooted tree exactly twice, hence is the contour walk of a rooted plane tree; such contour data has at most \(4^k\) possibilities.  To reconstruct the original canonical walk, choose the exceptional times and, for each exceptional non-tree traversal, its endpoint among previously exposed vertex slots; this costs at most \(k^{C_1(s+r)}=k^{C_1\delta}\).  The remaining local choices are from a fixed finite alphabet of opening and closing moves and contribute only another \(C_1^k\).  This proves (1).

For any fixed canonical pattern with \(q=k+1-\delta\) support vertices, the labels of the support vertices can be chosen in at most \((2C_0 n)^q\) ways.  Therefore
\[
N_k(X,Y)
\le
\sum_{\delta=0}^k C_2^k k^{C_2\delta} n^{k+1-\delta}
=C_2^k n^{k+1}\sum_{\delta=0}^k \left(\frac{k^{C_2}}{n}\right)^\delta .
\]
If \(k^{C_*}\le n\) with \(C_*\) large enough, the last sum is bounded by an absolute constant.  Enlarging \(C\) proves the claimed estimate.

# lemma lem:feature-isometry

## statement
Let \(G=(A,B,E)\) be a fixed bipartite graph with a matching saturating \(B\).  For each vertex \(z\in A\cup B\), let \(\Omega_z\) be a finite label set, and assume all nonempty \(\Omega_z\) have sizes between \(c n\) and \(C n\), where \(c,C>0\) are fixed constants.  The sets \(\Omega_z\) are pairwise disjoint.  Define
\[
Z_G(x,y)=\left(\prod_{a\in A}|\Omega_a|^{-1/2}\right)
\prod_{(a,b)\in E}\varepsilon_{x_a,y_b},
\]
with rows indexed by \(x\in\prod_{a\in A}\Omega_a\) and columns indexed by \(y\in\prod_{b\in B}\Omega_b\).  Then
\[
\mathbb E\|Z_G\|^2\le C_G .
\]

## proof
It suffices to prove a high even moment bound.  Let \(a=|A|\), \(b=|B|\), and choose a matching \(b'\mapsto a_{b'}\) saturating \(B\).  For \(k\ge1\), expand
\[
\mathbb E\operatorname{tr}\bigl((Z_G^\top Z_G)^k\bigr).
\]
The trace expansion sums over \(k\) row labelings \(x^1,\ldots,x^k\) and \(k\) column labelings \(y^1,\ldots,y^k\), with \(y^{k+1}=y^1\).  The normalization contributes \(\prod_{a\in A}|\Omega_a|^{-k}\).

If a summand is nonzero, each Rademacher variable appears an even number of times.  Since the sets \(\Omega_z\) are pairwise disjoint, a Rademacher variable contributed by the shape edge \((a_{b'},b')\) cannot coincide with a variable contributed by any different shape edge.  Thus the parity constraint for this matched edge must hold inside the factors coming from this edge alone.  For \((a_{b'},b')\), the labels
\[
y_{b'}^1,x_{a_{b'}}^1,y_{b'}^2,x_{a_{b'}}^2,\ldots,
y_{b'}^k,x_{a_{b'}}^k,y_{b'}^1
\]
form a closed alternating walk in the complete bipartite graph
\(\Omega_{b'}\times \Omega_{a_{b'}}\), and every traversed edge is repeated.  Lemma lem:even-bipartite-walk-count gives at most \(C_G^k n^{k+1}\) choices for these \(2k\) labels whenever \(k^{C_G}\le n\).

Doing this for all \(b'\in B\) gives at most \(C_G^k n^{b(k+1)}\) choices for matched coordinates.  The remaining \(a-b\) row coordinates contribute at most \(C_G^k n^{k(a-b)}\) choices.  Extra edges of \(G\) only add parity constraints.  Since all \(|\Omega_a|\) are comparable to \(n\),
\[
\mathbb E\operatorname{tr}\bigl((Z_G^\top Z_G)^k\bigr)
\le C_G^k n^{-ak} n^{b(k+1)} n^{k(a-b)}
=C_G^k n^b .
\]
Taking \(k=\lceil\log n\rceil\), which satisfies \(k^{C_G}\le n\) for all sufficiently large \(n\), we get
\[
\mathbb E\|Z_G\|^2
\le \left(\mathbb E\|Z_G\|^{2k}\right)^{1/k}
\le \left(C_G^k n^b\right)^{1/k}
\le C'_G .
\]

# lemma lem:separated-upper

## statement
Let \(H=(U,W,E)\) be a fixed bipartite graph.  Let \(\tau\) be its minimum vertex-cover size.  For each \(z\in U\cup W\), let \(\Omega_z\subset[n]\) be pairwise disjoint label sets, all of sizes between \(c n\) and \(C n\).  Let \(M_{H,\Omega}\) be the matrix with rows indexed by \(\prod_{u\in U}\Omega_u\), columns indexed by \(\prod_{w\in W}\Omega_w\), and entries
\[
M_{H,\Omega}(x,y)=\prod_{(u,w)\in E}\varepsilon_{x_u,y_w}.
\]
Then
\[
\mathbb E\|M_{H,\Omega}\|\le C_H n^{(|U|+|W|-\tau)/2}.
\]

## proof
Let \(S\) be a minimum vertex cover of \(H\), and write
\[
S_U=S\cap U,\qquad S_W=S\cap W,\qquad
I_U=U\setminus S,\qquad I_W=W\setminus S.
\]
By König's theorem, \(H\) has a matching of size \(\tau=|S|\), and every such maximum matching saturates \(S\).  Hence every vertex of \(S_W\) is matched to a distinct vertex of \(I_U\), and every vertex of \(S_U\) is matched to a distinct vertex of \(I_W\).

Define normalized feature matrices
\[
Z_L(x,r)=\left(\prod_{u\in I_U}|\Omega_u|^{-1/2}\right)
\prod_{(u,w)\in E,\ u\in I_U,\ w\in S_W}\varepsilon_{x_u,r_w},
\]
with rows \(x\in\prod_{u\in I_U}\Omega_u\) and columns \(r\in\prod_{w\in S_W}\Omega_w\), and
\[
Z_R(y,\ell)=\left(\prod_{w\in I_W}|\Omega_w|^{-1/2}\right)
\prod_{(u,w)\in E,\ u\in S_U,\ w\in I_W}\varepsilon_{\ell_u,y_w}.
\]
The matching observation is exactly the hypothesis of Lemma lem:feature-isometry for both \(Z_L\) and \(Z_R\), so \(\mathbb E\|Z_L\|^2\) and \(\mathbb E\|Z_R\|^2\) are bounded by constants depending only on \(H\).

Because \(S\) covers all edges, there are no edges between \(I_U\) and \(I_W\).  For unit vectors \(\xi,\eta\), group \(\xi\) by \(\ell\in\prod_{S_U}\Omega\) and \(\eta\) by \(r\in\prod_{S_W}\Omega\).  The bilinear form factors as
\[
|\langle \xi,M_{H,\Omega}\eta\rangle|
\le
\left(\prod_{z\in I_U\cup I_W}|\Omega_z|^{1/2}\right)
\left(\sum_{\ell,r}|\langle \xi_\ell,Z_L(\cdot,r)\rangle|^2\right)^{1/2}
\left(\sum_{\ell,r}|\langle \eta_r,Z_R(\cdot,\ell)\rangle|^2\right)^{1/2}.
\]
The two sums are at most \(\|Z_L\|^2\) and \(\|Z_R\|^2\), respectively.  Hence
\[
\|M_{H,\Omega}\|
\le
\left(\prod_{z\in I_U\cup I_W}|\Omega_z|^{1/2}\right)\|Z_L\|\|Z_R\|.
\]
Taking expectation and using Cauchy-Schwarz gives
\[
\mathbb E\|M_{H,\Omega}\|
\le C_H n^{(|I_U|+|I_W|)/2}
=C_H n^{(|U|+|W|-\tau)/2}.
\]

# lemma lem:color-coding-upper

## statement
For the injective graph matrix \(M_\alpha\) in the problem statement,
\[
\mathbb E\|M_\alpha\|\le C_\alpha n^{(|V(\alpha)|-\tau(\alpha))/2}.
\]

## proof
By Lemma lem:same-side-edges-and-cover-exponent, delete same-side edges and let \(H_\alpha\) be the remaining bipartite graph.  Put \(v=|V(\alpha)|\).  Choose uniformly a balanced ordered partition
\[
[n]=\bigsqcup_{a\in V(\alpha)}\Omega_a
\]
with all \(|\Omega_a|\) equal to either \(\lfloor n/v\rfloor\) or \(\lceil n/v\rceil\).

For such a partition \(\Omega\), let \(M^\Omega\) be the matrix obtained by retaining only those realization terms for which the label of vertex \(a\) lies in \(\Omega_a\).  Since the color classes are disjoint, this is exactly a separated-label matrix of the form in Lemma lem:separated-upper, embedded into the original row and column spaces.

For any fixed injective realization \(\varphi\), the probability over the random balanced partition that \(\varphi(a)\in\Omega_a\) for every \(a\in V(\alpha)\) is
\[
p_n=\frac{\prod_{a\in V(\alpha)}|\Omega_a|}{n(n-1)\cdots(n-v+1)},
\]
which is bounded below by a positive constant depending only on \(\alpha\).  Therefore, entrywise,
\[
\mathbb E_\Omega M^\Omega=p_n M_\alpha .
\]
Thus
\[
\|M_\alpha\|
\le p_n^{-1}\mathbb E_\Omega\|M^\Omega\|.
\]
Taking expectation over the Rademacher signs and applying Lemma lem:separated-upper to each balanced partition gives
\[
\mathbb E\|M_\alpha\|
\le C_\alpha n^{(|V(\alpha)|-\tau(\alpha))/2}.
\]

# lemma lem:lower-bound

## statement
For the injective graph matrix \(M_\alpha\),
\[
\|M_\alpha\|\ge c_\alpha n^{(|V(\alpha)|-\tau(\alpha))/2}
\]
for all sufficiently large \(n\).  Consequently the same lower bound holds for \(\mathbb E\|M_\alpha\|\).

## proof
Again delete same-side edges, which only apply row and column sign changes.  Let \(S\) be a minimum vertex cover of the cross-edge graph, and write
\[
S_U=S\cap U_\alpha,\qquad S_W=S\cap W_\alpha,\qquad
I_U=U_\alpha\setminus S,\qquad I_W=W_\alpha\setminus S .
\]
Fix one injective assignment of distinct labels to the vertices of \(S\).  Then restrict further to rows and columns whose free coordinates lie in the complement of these fixed labels, are internally distinct, and are disjoint from each other.  In other words, after the \(S\)-labels have been fixed, the remaining row coordinates range over ordered distinct \(I_U\)-tuples from an \(N=n-|S|\) point set, the remaining column coordinates range over ordered distinct \(I_W\)-tuples from the same set, and a matrix entry is retained exactly when the two free tuples are disjoint.

Since \(I_U\cup I_W\) is independent in the cross-edge graph, no remaining edge joins a free \(I_U\)-vertex to a free \(I_W\)-vertex.  Therefore, on this restricted submatrix, all random signs factor as a row sign times a column sign times one fixed sign.  Thus the restricted submatrix is obtained from the deterministic disjointness matrix
\[
D_{p,q,N},\qquad p=|I_U|,\quad q=|I_W|,\quad N=n-|S|,
\]
by multiplying rows and columns by signs.  Here \(D_{p,q,N}\) has rows indexed by ordered distinct \(p\)-tuples from an \(N\)-point set, columns indexed by ordered distinct \(q\)-tuples from the same set, and entry \(1\) exactly when the two tuples are disjoint.

The norm of \(D_{p,q,N}\) is \(\Theta_{p,q}(N^{(p+q)/2})\).  The upper bound is its Frobenius norm.  For the lower bound, apply it to the all-ones vector on columns: every row has
\[
(N-p)(N-p-1)\cdots (N-p-q+1)=\Theta_{p,q}(N^q)
\]
ones, and the number of rows is \(\Theta_p(N^p)\) while the number of columns is \(\Theta_q(N^q)\).  Hence the all-ones test vector gives a singular value \(\Theta_{p,q}(N^{(p+q)/2})\).

The restricted submatrix is a submatrix of \(M_\alpha\), so
\[
\|M_\alpha\|\ge c_\alpha n^{(p+q)/2}
=c_\alpha n^{(|V(\alpha)|-\tau(\alpha))/2}.
\]

# theorem thm:prob-16

## statement
Let $(\varepsilon_{i,j})_{i<j}$ are i.i.d.\ Rademacher random variables (i.e., uniform in $\{ -1,+1 \}$). In addition, let $\alpha$ be a shape (a fixed graph) in which we partition the vertices $V(\alpha)$ into the left $(U_\alpha)$ and right $(W_\alpha)$ sides, and let $n$ be a large integer. A realization is any injective map $\varphi:V(\alpha) \to [n]=\{ 1,\ldots,n \}$ from the shape vertices to the ground set $[n]$. The graph matrix $M_\alpha$ is the $n^{|U_\alpha|} \times n^{|W_\alpha|}$ random matrix, whose rows and columns are indexed by ordered subsets of $[n]$ with cardinalities $|U_\alpha|$ and $|W_\alpha|$, respectively, given by
\begin{align*}
    M_\alpha = \sum_{ \text{realization } \varphi } \left( \prod_{(i,j) \in E(\alpha)} \varepsilon_{\varphi(i),\varphi(j)} \right) e_{\varphi(U_\alpha)} e_{\varphi(W_\alpha)}^{\top} \,.
\end{align*}

Prove or disprove that there are functions $f$ and $g$ depending only on the shape $\alpha$ and a constant $C=C(\alpha)$, such that
    \begin{align*}
        C^{-1} n^{f(\alpha)} (\log n)^{g(\alpha)} \leq \mathbb E\left[ \|M_\alpha\| \right] \leq C n^{f(\alpha)} (\log n)^{g(\alpha)} \,.
    \end{align*}

## proof
The assertion is true.  Let \(H_\alpha\) be the bipartite graph of cross edges of \(\alpha\), and let
\[
\tau(\alpha)=\min\{|S|:S\subseteq V(H_\alpha)\text{ meets every edge of }H_\alpha\}.
\]
Define
\[
f(\alpha)=\frac{|V(\alpha)|-\tau(\alpha)}2,\qquad g(\alpha)=0.
\]

Lemma lem:color-coding-upper gives
\[
\mathbb E\|M_\alpha\|\le C_\alpha n^{(|V(\alpha)|-\tau(\alpha))/2}.
\]
Lemma lem:lower-bound gives
\[
\mathbb E\|M_\alpha\|\ge c_\alpha n^{(|V(\alpha)|-\tau(\alpha))/2}.
\]
Absorbing \(c_\alpha^{-1}\) and \(C_\alpha\) into one constant \(C=C(\alpha)\), we obtain
\[
C^{-1}n^{f(\alpha)}(\log n)^{g(\alpha)}
\le \mathbb E\|M_\alpha\|
\le C n^{f(\alpha)}(\log n)^{g(\alpha)}.
\]
Thus the required functions exist, and in fact no logarithmic factor is needed in this two-sided no-hidden-vertices formulation.
