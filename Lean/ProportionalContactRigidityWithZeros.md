# Selected-edge rigidity with vanishing factors (paper proof)

**Status.** The normalized-product identity and the zero-free
incidence theorem are checked in [ProportionalContactRigidity.lean](MOC/ProportionalContactRigidity.lean).
The extension below is a paper proof, not a claimed Lean theorem. It uses
gap-free contact isolation from the transfer stemming from
[Zheng's preprint, DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923).

**Proposition.** Let a fixed unitary have a contact-maximal strict witness in
order $n\ge4$, with both spectra injective. The mixed sums $a_i+b_j$ may
vanish. Choose any one vanishing factor from every zero contact. Form $E$
from the chosen zero edges and all edges of the nonzero contacts, or take
any superset of those edges. Then the only solutions to
$$
x_i+y_j=\ell_i(a_i+b_j)\qquad ((i,j)\in E)
$$
are $x_i=d a_i+c$, $y_j=d b_j-c$, $\ell_i=d$. Consequently,
$|E|\ge 3n-2$. The bound holds for every choice of zero factors.

**Proof.** Call a cell allowed if $a_i+b_j\ne0$. Injectivity of the
spectra says that every row and column has at most one forbidden cell.
Under the affine spectral motion with velocities $x,y$, normalize the
matching products by $D(t)=\prod_i(1+t\ell_i)$. Each nonzero contact's
product scales by $D(t)$, and each zero contact remains zero because the
chosen edge satisfies $x_i+y_j=0$. For $t$ near zero the denominator is
nonzero and the normalized profile is exact by a common $n$-th-root
scaling. Gap-free isolation makes the normalized profile constant near
zero. Clearing the denominator gives a polynomial identity for every
matching by infinitely many distinct values of $t$.

For an allowed cell put $m_{ij}=(x_i+y_j)/(a_i+b_j)$. For each
permutation using only allowed cells, cancel its nonzero constant product
to see that its product of factors $1+t m_{ij}$ equals $D(t)$.

Take any fully allowed two-by-two rectangle on distinct rows $i,k$ and
columns $j,l$. To extend $j\mapsto i,\ l\mapsto k$ to a permissible
matching, take an extension that minimizes the number of forbidden cells
elsewhere. If a forbidden cell is still used, swap its assigned row with
the row assigned to any other free column. The latter exists because
$n-2\ge2$. After the switch both cells are allowed: the bad row has no
other forbidden column and the bad column no other forbidden row.
This contradicts minimality. Switching the two prescribed assignments in
the resulting allowed matching yields another allowed matching. Cancel
the common polynomial factors (their constants are 1) to obtain
$$
(1+t m_{ij})(1+t m_{kl})=(1+t m_{kj})(1+t m_{il}).
$$
The coefficients of $t,t^2$ yield, respectively,
$$
m_{ij}+m_{kl}=m_{kj}+m_{il},\qquad
m_{ij}m_{kl}=m_{kj}m_{il}.
$$

Consider distinct rows $i,k$ and any column $j$ allowed in both. They
share at least $n-2$ allowed columns, so choose another such column
$l$. The first equation gives $d'=m_{ij}-m_{kj}=m_{il}-m_{kl}$;
using this in the second equation gives
$d'(m_{kl}-m_{kj})=0$. If $d'\ne0$, the slopes in each row would
be constant across $j,l$. Subtracting $x_i+y_j=m_{ij}(a_i+b_j)$
and $x_i+y_l=m_{il}(a_i+b_l)$ would then give
$y_j-y_l=m_{ij}(b_j-b_l)$; the other row gives the same formula
with $m_{kj}$. Since $b_j\ne b_l$, this contradicts $d'\ne0$.
Thus within each column the allowed slopes have one value $s_j$.
Any two distinct columns share at least two allowed rows $i,k$; subtracting
within each of the two columns gives $x_i-x_k=s_j(a_i-a_k)$ and
$x_i-x_k=s_l(a_i-a_k)$, so $s_j=s_l=d$ by injectivity of $a$.

The equations on the entire allowed set now read
$x_i-da_i=-(y_j-db_j)$. Any two distinct rows share an allowed
column, so the left-hand side is one constant $c$. Every column has
an allowed row, so $y_j=db_j-c$. By the checked distinct-contact
result there is at least one nonzero contact; it uses one allowed
edge in every row. Substitution in its incidence equations forces
$\ell_i=d$ in every row. Finally, the map from the $3n$ complex
variables to the residuals on $E$ has kernel of dimension two
(the common scale and translate), which gives the count. $\square$
