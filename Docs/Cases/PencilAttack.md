# Two moving spectral coordinates: checkpoint

The proved one-coordinate certificate and the exact fixed-partner matrix used below are in [Regular.md](Regular.md). This note records the next attempted reduction and its numerical status at the research pause.

## Rank-one separation test

In the homogeneous chart with first two diagonal entries \(0,\infty\), let the other two entries be \(x,y\). The infinity entry means taking the leading coefficient in that entry. For \(\pi=(i,j,k,l)\) in one-line notation the normalized vertex is
\[
z_\pi(x,y)=b_i(x+b_k)(y+b_l).
\]
Use the coordinate order \((xy,x,y,1)\), so its complex coefficient vector is \(v_\pi=(b_i,b_i b_l,b_i b_k,b_i b_k b_l)\). For real orthogonal \(R\), the actual coefficient vector is \(v=\sum_\pi c_\pi v_\pi\) with \(c_\pi=\operatorname{sgn}(\pi)\prod_m R_{m,\pi(m)}/\det R\), by the determinant expansion. Normalization of the two fixed entries is available for distinct entries by a common Möbius transformation on the signed spectra. It suffices to work with the leading coefficients in the normalized chart because common projective changes and rescaling of the individual homogeneous representatives multiply all terms by the same nonzero scalar.

For this fixed \((R,b)\), simultaneous scalar MOC for all \((x,y)\) holds exactly when the strict separating cone
\[
\{ s\in\mathbb C^4:\ \Re\sum_{j=1}^4 s_j(v-v_\pi)_j>0\text{ for all }\pi\}
\]
misses the complex quadric \(s_1s_4=s_2s_3\). In fact a failure at a finite pair produces \(s=\eta(xy,x,y,1)\) for a separating phase \(\eta\). Conversely, any point of the quadric with \(s_4\ne0\) has that form up to positive rescaling, and such points are dense in the quadric by the rank-one factorization of \(2\times2\) matrices. The cone is open, so its intersection with the quadric would contain such a finite witness. This proves both implications. The quadric constraint disappears for a one-coordinate pencil, where the previous coefficient-hull lemma applies. Requiring the full cone to be empty gives the stronger assertion that a single probability law works for the entire two-coordinate pencil.

## Three-coordinate fixed-anchor test

Put the first coordinate at infinity, leaving three independent entries. The normalized vertices are \(\prod_{r=2}^4(x_r+b_{\pi(r)})\). A common law is a linear feasibility problem in 24 nonnegative probabilities. For simple \(b\), the matrix of real coefficient evaluations, including normalization, has rank at most 12. Indeed its homogeneous leading coefficient contributes one real coordinate, and the other seven complex coefficients contribute fourteen. Specializing \(x_2=x_3=x_4=t\) gives \(\prod_{j\ne\pi(1)}(t+b_j)\). Its three complex nonleading coefficients and its leading coefficient belong to a real span of at most four vectors. The specialization map onto these seven real coordinates from the ambient fifteen-dimensional space is surjective (choose one monomial coefficient in each degree). Hence there are at least three independent real linear relations. The coefficient matching still imposes many more conditions than the scalar problem.

## Numerical observations awaiting exact certification

All observations below used floating-point NumPy/SciPy, with the lexicographic permutation list. They do not prove positive laws or strict impossibility.

* For the matrix \(R\) and partner \(b=(1+i,2-i,-1+2i,-2-2i)\) in Regular.md, the common three-coordinate law LP reported feasibility with the first **finite** entry fixed at each of \(-1,0,1,2+i\). The coefficient matrix had numerical rank 12 in all four cases. A rational basis and positive weights were not recovered before the pause.
* For that same \(R\), a three-coordinate law LP in the infinity chart reported infeasibility at \(b=(-2-2i,-2-i,1+3i,1-3i)\). No exact separator was certified.
* For the two-coordinate chart the same \(R\) and \(b=(1,3-2i,-2-i,(1-i)/2)\) gave a numerical separator. In the vector order \((1,\Re v_1,\dots,\Re v_4,\Im v_1,\dots,\Im v_4)\) the approximate coefficients are \((-192.99657534,36.61986301,-219.71917808,73.23972603,75.21917808,-292.95890411,-622.53767123,-109.85958904,208.83219178)\). The optimization imposed nonnegative costs on permutation columns and cost \(-1\) on the signed target. Decimal rounding at active constraints prevents treating this output as an exact certificate. Even an exact separator for this affine LP would disprove only its common-weight assertion, unless the separating cone is also shown to meet the rank-one quadric.
* A second numerical separation was obtained on a relabeling of the spin rotation \(\operatorname{Sym}^3\left(\begin{smallmatrix}4/5&3/5\\-3/5&4/5\end{smallmatrix}\right)\) in the normalized monomial basis, at \(b=(1,-1+3i,3-i,(1-i)/1000)\). Here the spin theorem already proves scalar MOC for every spectrum, so certifying this separation would distinguish the two quantifiers on a proved scalar family. The numeric relabeling used zero-based rows \((1,0,2,3)\) and columns \((3,1,0,2)\), with cubic matrix given by the columns of the substitution \((X,Y)\mapsto(4X/5-3Y/5,3X/5+4Y/5)\).

The unresolved global implication is exclusion of **rank-one** separators for every partner and mixer. The general three-coordinate positive law, an exact disproof of the stronger two-coordinate law, and a proof of unrestricted MOC were not established in this checkpoint.
