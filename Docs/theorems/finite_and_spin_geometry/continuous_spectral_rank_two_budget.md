# The actual spectral budget for a complex two-dimensional plane

## 1. Scope and notation

Let $A=\operatorname{diag}(a_i)$, $B=\operatorname{diag}(b_i)$, and

\[
z_\pi=\prod_i(a_i+b_{\pi(i)}),\qquad
F(V)=\Re\{\eta\det(A+U_Y(V)BU_Y(V)^*)\},
\quad U_Y(V)=I+Y(V-I_2)Y^*.
\]

Here $Y^*Y=I_2$, its rows are $y_i\in\mathbb C^{1\times2}$, and $W_i=y_i^*y_i$.

**Maximizing-base hypothesis for Sections 2–7:** the chosen identity pairing itself attains the permutation support height,

\[
h=\Re(\eta z_{\mathrm{id}})=\max_\pi\Re(\eta z_\pi). \tag{1}
\]

This hypothesis cannot be obtained for a given relative rank-two update merely by reordering $b$: such a reordering changes the base permutation and can destroy rank-two distance. For a nonmaximizing base, the exact test is the prescribed-height $6\times6$ pencil of `continuous_full_rank_two_geometry.md`, with $c=h-F(I_2)>0$. All statements below retain this distinction.

Put

\[
\delta_{ij}=h-\Re(\eta z_{(ij)})\ge0,\quad
L_{ij}(T)=y_iTy_j^*,\quad
\mathcal A(T,T)=\sum_{i<j}\delta_{ij}|L_{ij}(T)|^2. \tag{2}
\]

For a canonical triple (i<j<k), define

\[
s_{ijk}=\Re\{\eta(z_{(ijk)}-z_{(ikj)})\},\qquad
C_{ijk}(T)=-\Im\operatorname{tr}(\operatorname{adj}(W_i)W_jTW_k). \tag{3}
\]

Finally let $R=I-2YY^*$ and $g=h-\Re\{\eta\det(A+RBR)\}$. This reflection gap is an actual determinant quantity. Its required lower bound is the central unresolved inequality, not an assumed positivity property.

## 2. The exact second and third derivatives

At this commuting base the first derivative vanishes. For the directional Hessian in the convention of the full-plane note,

\[
\boxed{H(T,T)=-2\mathcal A(T,T),\qquad
\ell(T)=4\sum_{i<j<k}s_{ijk}C_{ijk}(T).} \tag{4}
\]

These coefficients use the actual spectral determinant products. They are not free coefficients of a Boolean or common-minor relaxation.

### 2.1 The spectral three-label identity

The matrix $(a_i+b_j)$ has rank at most two. Its $3\times3$ determinant identity, multiplied by the fixed factors outside a triple, is

\[
z_{\mathrm{id}}-z_{(ij)}-z_{(ik)}-z_{(jk)}+z_{(ijk)}+z_{(ikj)}=0. \tag{5}
\]

If $p=h-\Re(\eta z_{(ijk)})$ and $q=h-\Re(\eta z_{(ikj)})$, (1) and (5) give

\[
p,q\ge0,\qquad
p+q=\delta_{ij}+\delta_{ik}+\delta_{jk},\qquad
s_{ijk}=q-p.
\]

In particular,

\[
|s_{ijk}|\le\delta_{ij}+\delta_{ik}+\delta_{jk}. \tag{6}
\]

### 2.2 Direct third-order expansion, including cancellation of diagonal terms

For skew-Hermitian $X$, put $U(t)=e^{tX}$. The exact identity

\[
\det(A+UBU^*)=\frac{\det((a_i+b_j)U_{ij})}{\det U}
\]

and the determinant expansion give

\[
\det(A+U(t)BU(t)^*)
=z_{\mathrm{id}}
+t^2\sum_{i<j}(z_{(ij)}-z_{\mathrm{id}})|X_{ij}|^2
+t^3\sum_{i<j<k}(z_{(ijk)}-z_{(ikj)})\Re(X_{ij}X_{jk}X_{ki})
+O(t^4). \tag{7}
\]

Here is a cancellation proof of the cubic term. Divide each permutation product by the product of the diagonal entries of (U(t)). A transposition ratio has quadratic term $X_{ij}X_{ji}$, and its cubic contribution from a third label $k$ is one half of the sum of the two oriented cycle products. The terms involving $X_{ii}+X_{jj}$ cancel against the diagonal denominator. Each three-cycle ratio contributes its oriented product at order three. On combining the three transpositions and the two cycles belonging to one triple, identity (5) cancels the orientation-even cubic coefficient. Since the reversed skew-Hermitian cycle product is the negative complex conjugate of the forward one, the surviving term is exactly the real part displayed in (7).

Now set $X=iYTY^*$. Then

\[
\Re(X_{ij}X_{jk}X_{ki})
=\Im\operatorname{tr}(TW_iTW_jTW_k).
\]

For arbitrary $2\times2$ matrices, the polynomial identity

\[
TWT=\operatorname{tr}(TW)T-\det(T)\operatorname{adj}(W)
\]

holds. For Hermitian $T,W_i,W_j,W_k$, $\operatorname{tr}(TW_i)$ and $\operatorname{tr}(TW_jTW_k)$ are real. Consequently

\[
\Im\operatorname{tr}(TW_iTW_jTW_k)
=\det(T) C_{ijk}(T). \tag{8}
\]

Equations (7)–(8) give $F'''(T)=6\det(T)\sum s_{ijk}C_{ijk}(T)$. Comparing with the independently derived Cayley identity $F'''(T)=(3/2)\det(T)\ell(T)$ proves (4), including the factor four. The quadratic term of (7) proves the Hessian formula.

## 3. The exact matrix budget, under the maximizing-base hypothesis

Let $\mathcal A_4$ be the real $4\times4$ matrix of (2) on Hermitian $T=\left(\begin{smallmatrix}s&x+iy\\x-iy&t\end{smallmatrix}\right)$. The full-plane theorem gives

\[
F(V(T))-h=
\frac{-4\mathcal A(T,T)+2\det(T)\ell(T)-g\det(T)^2}{D(T)}. \tag{9}
\]

Thus, **when (1) holds**, nonascent on the entire fixed plane is equivalent to

\[
\begin{pmatrix}4\mathcal A_4&-\ell\\-\ell^T&g\end{pmatrix}\succeq0. \tag{10}
\]

Equivalently, $\ell$ must annihilate $\ker\mathcal A_4$, and

\[
\boxed{g\ge\frac14\ell^T\mathcal A_4^+\ell.} \tag{11}
\]

The right side is a nonnegative quadratic coherence energy. In this actual spectral setting, the explicit edge representation in the next section already proves the kernel condition. The remaining issue is the scalar comparison (11).

The weaker statement $g\ge0$ is insufficient when $\ell\ne0$. By the endpoint identity in the full-plane note, $\ell$ is the gradient at the reflection endpoint, pulled back by the $2\times2$ adjugate. Thus (11) bounds an actual endpoint gradient by the support loss and the base Hessian.

## 4. A constructive coherent-edge sum of squares

Let $p_{ij}=\det\left(\begin{smallmatrix}y_i\\y_j\end{smallmatrix}\right)$, with $p_{ji}=-p_{ij}$. Direct multiplication gives the Plücker form of (3):

\[
C_{ijk}(T)=-\Im\{p_{ik}\overline{p_{ij}}L_{jk}(T)\}. \tag{12}
\]

This expression is cyclically invariant and changes sign under reversal. Define

\[
\chi_{ijk}=\frac{s_{ijk}}{\delta_{ij}+\delta_{ik}+\delta_{jk}},\qquad |\chi_{ijk}|\le1,
\]

and put $\chi_{ijk}=0$ if the denominator vanishes; (6) then gives $s_{ijk}=0$. For an ordered edge (i<j), set

\[
A_{ij}^{\rm flow}
=\sum_{k\ne i,j}\epsilon_{ijk}\chi_{\{i,j,k\}}p_{kj}\overline{p_{ki}},
\qquad a_{ij}=-i\overline{A_{ij}^{\rm flow}}, \tag{13}
\]

where $\epsilon_{ijk}$ is the parity sign taking the increasing order of the triple to ((i,j,k)).

Then

\[
\ell(T)=4\sum_{i<j}\delta_{ij}\Re\{\overline{a_{ij}}L_{ij}(T)\}. \tag{14}
\]

**Proof.** In one triple, use (12) on each of its three edges, inserting the cyclic or reversal sign. The contribution from that triple to the right side of (14), divided by four, is

\[
\chi_{ijk}(\delta_{ij}+\delta_{ik}+\delta_{jk})C_{ijk}(T)
=s_{ijk}C_{ijk}(T).
\]

Summing proves the identity. Zero denominators cause no division problem. In particular if $\mathcal A(T,T)=0$, every edge with positive $\delta_{ij}$ has $L_{ij}(T)=0$, and (14) gives $\ell(T)=0$. This establishes the kernel condition in (11) for all degeneracies.

Define the explicit flow energy

\[
C_{\rm flow}=\sum_{i<j}\delta_{ij}|a_{ij}|^2.
\]

Completing squares in (9) yields the exact polynomial identity

\[
\boxed{
(h-F(V(T)))D(T)
=4\sum_{i<j}\delta_{ij}|L_{ij}(T)-\det(T)a_{ij}|^2
+(g-4C_{\rm flow})\det(T)^2.} \tag{15}
\]

Thus, at a maximizing commuting pairing, $g\ge4C_{\rm flow}$ is a proved sufficient support certificate for every complex $V\in U(2)$, in every ambient dimension. Its inputs include the coherent Plücker phases and the actual rank-two spectral identities.

The chosen triangle allocation need not minimize energy. For any family of complex edge values representing $\ell/4$ as in (14), the same square completion works. In the real Hilbert space of edge values with norm squared $\sum\delta_{ij}|a_{ij}|^2$, the minimum representation energy is

\[
C_{\min}=\frac1{16}\ell^T\mathcal A_4^+\ell. \tag{16}
\]

This follows by the least-norm solution of the adjoint of $T\mapsto(L_{ij}(T))$; its Gram operator is exactly $\mathcal A_4$. Hence minimizing the edge flow recovers the necessary-and-sufficient budget (11).

The universal optimized inequality $g\ge4C_{\min}$ remains unproved for actual spectra and planes satisfying (1). The exact repaired flow example is in `optimized_triangle_flow_example.md`; no universal bound for the prescribed triangle allocation is asserted.

## 5. An exact genuinely complex plane with a complete certificate

Take $\eta=1$,

\[
a=(1+i,\ 2-i,\ -1+2i,\ -2-3i),\quad
b=(2+i,\ 3-2i,\ -1+3i,\ 1-i),
\]

\[
Y=\frac12\begin{pmatrix}1&1\\1&i\\1&-1-i\\1&0\end{pmatrix}.
\]

Then $Y^*Y=I_2$, the identity is a permutation support maximizer, and $h=459$. This plane cannot be made real by diagonal row phases and a frame change: for $P=YY^*$,

\[
P_{12}P_{23}P_{31}=(-1+i)/64,
\]

whose nonzero imaginary part is invariant under those row phases.

The six transposition gaps, in order $12,13,14,23,24,34$, are

\[
(95,187,335,393,160,456).
\]

In coordinates $s,t,x,y$,

\[
\mathcal A_4=\begin{pmatrix}
813/8&-145/4&-419/16&-97/4\\
-145/4&1255/16&-111/16&301/16\\
-419/16&-111/16&3749/16&-485/8\\
-97/4&301/16&-485/8&2925/16
\end{pmatrix},
\]

\[
\ell=(61/8,-13/4,165/8,-181/8)^T,\qquad g=2997/8.
\]

Thus the exact stationary support matrix is

\[
M_5=\begin{pmatrix}
-813/2&145&419/4&97&61/8\\
145&-1255/4&111/4&-301/4&-13/4\\
419/4&111/4&-3749/4&485/2&165/8\\
97&-301/4&485/2&-2925/4&-181/8\\
61/8&-13/4&165/8&-181/8&-2997/8
\end{pmatrix}.
\]

All leading principal minors of $-M_5$ are strictly positive. Independently, the explicit triangle flow has

\[
C_{\rm flow}=
\frac{64758518125711807423}{146435984769187756800},
\]

\[
g-4C_{\rm flow}=
\frac{13649886680413529040377}{36608996192296939200}>0.
\]

Hence the entire $U(2)$ plane has support at most 459, with strict inequality away from its identity action. These are exact rational statements.

The standalone certificate `code/theorems/finite_and_spin_geometry/continuous_full_rank_two_exact.py` uses only Gaussian rational arithmetic. It verifies all 24 vertex supports, the Hessian coefficients, the independent signed-Cayley and cycle computations of $\ell$, the full Cayley numerator at seven rational Hermitian matrices, both reflection endpoint derivative identities, every leading principal minor, and the exact edge-flow square completion. Its JSON companion records all coefficients and the flow. The general identities are proved above; finite evaluations are independent factor and sign checks, not substitutes for those proofs.

## 6. Real and gauge-real planes reduce the full complex action to one real circle

Suppose $Y$ is real and (1) holds. Since every squared minor is unchanged by entrywise conjugation, $F(U)=F(\overline U)$ in a diagonal spectral basis. On this real plane, conjugation sends $T$ to $-\overline T$, whose coordinates are

\[
(s,t,x,y)\longmapsto(-s,-t,-x,y).
\]

Consequently $\mathcal A_4$ splits the three real symmetric coordinates $s,t,x$ from the imaginary off-diagonal coordinate $y$, and $\ell$ has only a $y$-component. These assertions also follow immediately from the real Plücker expression (12).

The full $5\times5$ condition therefore splits into an automatically nonpositive $3\times3$ Hessian block and a $2\times2$ block on $y,d$. The latter is exactly the criterion for the single circle $T=y\left(\begin{smallmatrix}0&i\\-i&0\end{smallmatrix}\right)$, whose Cayley transform is a real plane rotation. Thus, **under (1)**,

\[
\boxed{F(V)\le h\ \forall V\in U(2)
\quad\Longleftrightarrow\quad
F(V)\le h\ \text{on the real rotation circle of that plane}.} \tag{17}
\]

The same holds if diagonal row phases and an internal $U(2)$ change of frame make $Y$ real. Those row phases commute with diagonal $A,B$ and preserve the determinant. This reduction does not cover a generic complex plane, as the explicit example above demonstrates. It also does not automatically prove the real rotation-circle inequality.

## 7. Cycle-reversible spectral data reduce to the reflection endpoint

Under (1), if every $s_{ijk}=0$, equation (4) gives $\ell=0$. The whole fixed complex plane is therefore bounded by $h$ exactly when $g\ge0$: only the reflection endpoint remains.

A support-independent sufficient condition is that the rows

\[
(1,b_i-a_i,a_i b_i)
\]

span a space of dimension at most two. Indeed the local oriented three-cycle difference equals the determinant of these three rows, and the outside diagonal factors give the full spectral product difference. Equivalently, a common nonzero relation

\[
\alpha a_i b_i+\beta(b_i-a_i)+\gamma=0
\]

annihilates every such difference. This includes $a_i=b_i$. In the isospectral case there is also the direct identity $\det(A+UAU^*)=\det(A+U^*AU)$, so inversion symmetry makes every odd derivative at the identity vanish.

The resulting reflection inequality has not been proved in all dimensions for all such spectra. The final batch proves it in dimension four whenever the identity base is a support maximizer, and proves the whole $U(4)$ support inequality if the complete vertex cost is inversion-even; see continuous_reversible_dimension_boundary.md. The categorical track's rank-two reflection without a common positive permutation law does not contradict this tangent-cone statement. Reflection scalar MOC outside the stated scope remains a separate question.

## 8. Two positive subclasses with carefully stated conclusions

### 8.1 A coordinate-containing plane gives a full scalar MOC class

This statement does **not** require the maximizing-base hypothesis. If the active plane contains a coordinate vector $e_i$, choose $Y=(e_i,v)$. For every $V\in U(2)$, a diagonal phase $D_z=\operatorname{diag}(z,1)$ can be chosen so that $\operatorname{rank}(D_zV-I_2)\le1$. If $V_{22}\ne1$, take

\[
z=\frac{V_{22}-1}{\det V-V_{11}}.
\]

The unitary identity $V_{11}=\det V\,\overline{V_{22}}$ gives $|z|=1$, and expansion of the $2\times2$ determinant gives $\det(D_zV-I_2)=0$. If $V_{22}=1$, unitarity already makes $V$ diagonal with its second entry one, so it is itself a rank-one update.

Lift $D_z$ to the diagonal phase acting only on coordinate $i$. Left multiplication by this phase preserves the actual determinant because it commutes with $A$, and the resulting relative unitary has rank-one difference from identity. The all-dimensional rank-one MOC theorem therefore proves scalar MOC for every unitary in this coordinate-containing rank-two class. The rank-one theorem and its independent finite-support proof were recorded in the first batch, with its known Drury priority explicitly acknowledged. No relabeling of the base is involved in this reduction.

### 8.2 A positive Gram kernel gives one aligned support direction for all unitaries

Suppose the normalized matrix

\[
C_{ij}=\frac{a_i+b_j}{a_i+b_i}
=\frac{\langle u_i,u_j\rangle}{\|u_i\|^2}
\]

is a normalized positive Gram kernel. For example, this occurs for $a_i=1/\overline{b_i}$, $b_i\ne0$, with $u_i=(1,b_i)$. Define

\[
w=(e_1\otimes u_1)\wedge\cdots\wedge(e_n\otimes u_n),\qquad
\Gamma(U)=(\det U)^{-1}\bigwedge^n(U\otimes I).
\]

The operator $\Gamma(U)$ is unitary, and the exterior-power inner-product determinant formula yields

\[
\frac{\det(A+UBU^*)}{z_{\mathrm{id}}}
=\frac{\langle w,\Gamma(U)w\rangle}{\|w\|^2}.
\]

Thus the absolute value of this normalized determinant is at most one, and

\[
1-\Re\frac{\det(A+UBU^*)}{z_{\mathrm{id}}}
=\frac{\|\Gamma(U)w-w\|^2}{2\|w\|^2}\ge0.
\]

Identity is a maximizing permutation in the aligned support direction $\eta=1/z_{\mathrm{id}}$, because every normalized permutation product also has modulus at most one. This proves that support direction for all $U$ and all dimensions. It does not prove full MOC in every support direction for this spectral class.

## 9. Four-label reflection structure and the outstanding bridge

For the exact low-rank expansion, put $P=YY^*$, $C_{ij}=a_i+b_j$, and $c_i=a_i+b_i$. Since $\det(I-2P)=1$,

\[
\det(A+RBR)=\det(C\circ R)
=\det\bigl(\operatorname{diag}(c_i)-2(C\circ P)\bigr).
\]

Moreover

\[
C\circ P=\operatorname{diag}(a)P+P\operatorname{diag}(b)
=[\operatorname{diag}(a)Y,\,Y]
\begin{bmatrix}Y^*\\Y^*\operatorname{diag}(b)\end{bmatrix}
\]

has rank at most four. Therefore the exact reflection expansion stops at four labels:

\[
\boxed{
\det(A+RBR)=
\sum_{|S|\le4}(-2)^{|S|}\det((C\circ P)_{S,S})\prod_{j\notin S}c_j.} \tag{18}
\]

For four labels, the determinant factors into the two corresponding $4\times4$ factor determinants. This is algebraic low rank, not positivity: neither factor is generally the conjugate of the other. The three-label budget (6) already controls the cubic term, but the required comparison with (18) remains unproved.

At an arbitrary global support maximum with $A$ diagonal and the conjugated $B$ normal, direct first variation also gives

\[
\eta[B,\operatorname{adj}(A+B)]\ \text{Hermitian},
\]

equivalently the negative of $\eta[A,\operatorname{adj}(A+B)]$. For distinct $a_i,a_j$, this implies equality of the moduli of the two transposed off-diagonal adjugate entries. These necessary conditions do not force commutation; no commutation conclusion is proved here. Every fixed plane at a global maximum also satisfies the full $5\times5$ nonascent criterion, but compatibility of all these matrices has not yet yielded the permutation bound.

The prior holomorphic finite-witness reduction, with complex rank-two bound 16 and real bound 12, remains compatible with these formulas. It reduces a strict scalar counterexample while preserving the relevant spectral construction and support. It does not justify resetting a surviving pairing to a maximizing permutation. No unrestricted complex MOC proof or scalar counterexample is claimed in this batch.
