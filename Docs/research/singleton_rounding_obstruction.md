# Exact obstruction to spectrum-dependent singleton rounding

The following stronger sufficient condition for MOC4 is false: for every pair
of complex spectra and every real orthogonal mixer, there are probability
weights on permutations that both recover the determinant and have singleton
marginals equal to the squared entries of the mixer. Allowing the weights to
depend on both spectra does not repair this condition.

Set

\[
 O=\frac1{59}\begin{pmatrix}
 -25&46&16&22\\-46&-31&20&-2\\-16&20&-11&-52\\22&2&52&-17
 \end{pmatrix},\quad
 a=(0,1,-2+2i,2-2i),\quad b=(2+i,-2-2i,1+i,2).
\]

Direct rational computation gives \(O^TO=I\), \(\det O=1\), and

\[
 d=\det(D_a+OD_bO^T)=\frac{94358-98282i}{3481}.
\]

Write \(z_\sigma=\prod_i(a_i+b_{\sigma(i)})\), and put

\[
 G=\begin{pmatrix}
124&24&108&0\\4&-136&44&0\\104&-776&416&0\\0&0&0&0
\end{pmatrix}.
\]

For every permutation, exact evaluation gives

\[
 7\Re z_\sigma+\Im z_\sigma
 \le 212+\sum_i G_{i,\sigma(i)}.
\]

The 24 slacks in lexicographic order are
\(136,0,204,180,160,272,0,0,24,0,160,136,
44,180,0,0,136,0,0,136,0,136,0,0\).
Consequently any probability law with singleton marginals
\(\Pr[\sigma(i)=j]=O_{ij}^2\) must obey

\[
 7\Re\mathbb E z_\sigma+\Im\mathbb E z_\sigma
 \le212+\sum_{i,j}G_{ij}O_{ij}^2
 =\frac{555832}{3481}.
\]

But \(7\Re d+\Im d=562224/3481\), a strict violation of
\(6392/3481\). This is an exact Farkas certificate of infeasibility. Its
strictness also makes the obstruction persist under sufficiently small
perturbations of spectra and mixer.

This is **not** a counterexample to MOC. In fact the same determinant is the
following explicit convex combination (permutations use zero-based indices):

\[
 d=\frac{1297906(36-72i)+1840019(26+2i)+95924(-72-16i)}{3233849}.
\]

The three products correspond respectively to permutations
\((1,3,0,2)\), \((2,1,3,0)\), and \((3,2,1,0)\). All three weights are positive
and sum to one. Thus a general MOC proof via probability weights must allow
the first-order assignment marginals themselves to change with the spectra.
Preserving the entire singleton sector, even only for the given spectra, is
already too much.

Reproduce the certificate with
`python code/research/verify_singleton_rounding_obstruction.py`.
