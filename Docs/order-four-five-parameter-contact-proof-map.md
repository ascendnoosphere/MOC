# Order-four contact family with rays 0, 7, 10, 18, and 22

[Proof map index](README.md) · [Conjecture and proof tree](../README.md#proof-tree) · [Order four](order-four-proof-map.md)

For normal matrices of order four, a matching product pairs the four
eigenvalues of the first matrix with the four eigenvalues of the
second. Fix a direction in the complex plane. A matching contact is a
permutation whose directional projection attains the selected
extremal value. The gap is the difference from that value.

This family uses nonnegative coefficients $a,b,c,d,e$ for the ordinary
rays 0, 7, 10, 18, and 22 in that order. A ray is a gap profile that
can be multiplied by any nonnegative real number. The mixed ray 34
has coefficient one. The common minimum projection is the signed
height $t$. The gaps at indices 7, 9, 12, 14, 15, 20, 22, and 23
are zero for all allowed coefficients. The permutation indices start
at zero and follow lexicographic order.
[Exact gap](../Lean/MOC/FourContact0710SpectralLift.lean#L18) · [Evaluation](../Lean/MOC/FourContact0710SpectralLift.lean#L33) · [Ray enumeration](https://github.com/ascendnoosphere/MOC/blob/a49606d39e8bb5903c9bb4a51651a18679499c0c/data/cone82.json)

```mermaid
flowchart TD
    A["Actual matching values with the prescribed gap"]
    B["Nonzero signed height and spectral lift equations"]
    C["Fourth weight d = 0"]
    D["Three explicit coefficient choices"]
    E["Contradiction to the radial gradient identity"]
    S["Shifted scalar quadratic and sign constraint"]
    T["Continuous scalar deformation to c = 0 and d = 1"]
    P["Positive quadratic term of the unequal factor product"]
    H["Actual Hessian determinant equals the factor product"]
    J["Actual spectral lift forces the branch polynomial to vanish"]
    O["Positive Hessian second difference for unequal weights"]
    N["Open Lean premise: the necessary spectral sign is nonpositive"]
    X["Exclude the unequal branch when the signed height is negative"]
    F["Equal first weights and negative signed height"]
    R["The imaginary radial gradient is nonnegative"]
    A --> B
    B --> C
    B --> D
    C --> E
    D --> E
    S --> T
    S --> P
    H --> J
    B --> J
    J --> O
    P --> O
    O --> X
    N -.-> X
    J --> F
    F --> R
    R --> E
```

| Step | Statement and scope | Lean source | Lean Checked? |
| --- | --- | --- | --- |
| Spectral coordinates | The prescribed gap and signed height give exact values for the 24 matchings. A spectral lift forces $F+tQ=0$, where $F=-(c+1)((a+1)(b+1)+e)$ and $Q=e(d-1)-1$. Thus $Q$ and $t$ are nonzero. | [Evaluation](../Lean/MOC/FourContact0710SpectralLift.lean#L33) · [Height](../Lean/MOC/FourContact0710SpectralLift.lean#L71) | Yes |
| Real lift equations | The imaginary coordinates of a spectral lift lie in the real matching Hessian kernel. The imaginary and real coordinates have the same cubic gradient. | [Real lift equations](../Lean/MOC/FourContact0710SpectralLift.lean#L99) | Yes |
| Fourth weight zero | Subtract Hessian rows 1 and 3. Since $t$ is nonzero, the imaginary coordinate $y_5$ is zero. Row 13 then gives $y_6=(e+1)y_0$. The imaginary radial gradient is $(e+1)y_0^2\ge0$. The real radial gradient is $-e-1<0$. The gradient identity is impossible. | [Boundary exclusion](../Lean/MOC/FourContact0710SpectralLift.lean#L158) | Yes |
| Unequal rational anchors | At $(a,b,c,d,e)=(0,4,0,1,10)$ and $(4,0,0,1,10)$ the height is $-15$. The imaginary radial gradient is $(y_0-y_1/11)^2+(6/605)y_1^2$. The real radial gradient is $-1$. | [Unequal anchor exclusion](../Lean/MOC/FourContact0710SpectralLift.lean#L205) | Yes |
| Equal rational anchor | At $(a,b,c,d,e)=(2,2,1,1,9)$ the height is $-36$. The imaginary radial gradient is $(35/27)y_0^2$. The real radial gradient is $-1$. | [Equal anchor exclusion](../Lean/MOC/FourContact0710SpectralLift.lean#L219) | Yes |
| Shifted quadratic | On the scalar branch, the polynomial in the five weights is $e^2 A(c+p(c+1)/e)$ when $e\ne0$, with $p=(a+1)(b+1)$ and $A$ a quadratic. For unequal nonnegative first weights and $d>0$, a positive root forces the constant term of $A$ to be negative. The root is unique. | [Shift](../Lean/MOC/FourContact0710ShiftedQuadratic.lean#L58) · [Positive root](../Lean/MOC/FourContact0710ShiftedQuadratic.lean#L129) | Yes |
| Scalar deformation | For a scalar point with branch polynomial zero and $Q<0$, reduce $c$ to zero at the fixed positive root. On that slice move $d$ to one and choose the positive root at each value of $d$. The reconstruction preserves the branch equation and $Q<0$. At the endpoint, $p>4$. | [Third weight](../Lean/MOC/FourContact0710ShiftedQuadratic.lean#L249) · [Fourth weight](../Lean/MOC/FourContact0710ShiftedQuadratic.lean#L305) · [Endpoint condition](../Lean/MOC/FourContact0710ShiftedQuadratic.lean#L355) · [Continuity of the root](../Lean/MOC/FourContact0710ShiftedQuadratic.lean#L393) | Yes |
| Scalar pencil sign | At the signed height $t<0$, both scalar pencil factors vanish when the branch polynomial is zero. The slope of the linear factor is positive. The slope of the quadratic factor is negative. Thus the quadratic coefficient of their product multiplied by $-4$ is positive for unequal first weights. | [Height identities](../Lean/MOC/FourContact0710PencilFactors.lean#L39) · [Slopes](../Lean/MOC/FourContact0710PencilFactors.lean#L119) · [Quadratic term](../Lean/MOC/FourContact0710PencilFactors.lean#L169) | Yes |
| Actual determinant | For $c\ge0$ and $d>0$, the leading eight rows and columns have determinant $d^2(c+1)^2$. The remaining six rows and columns give a Schur complement. This is the matrix after elimination of the first eight variables. Its rescaled determinant gives the exact product of the two scalar factors multiplied by $-4$. An actual lift forces the branch polynomial to vanish. | [Determinant](../Lean/MOC/FourContact0710HessianPencil.lean#L336) · [Branch equation](../Lean/MOC/FourContact0710HessianPencil.lean#L389) | No |
| Unequal spectral branch | Let $D(t)$ be the Hessian determinant at signed height $t$. If $a\ne b$, $d>0$, and $Q<0$, an actual lift would give $D(t+1)+D(t-1)-2D(t)>0$. The unequal branch is excluded if this second difference is nonpositive. | [Strict sign](../Lean/MOC/FourContact0710HessianPencil.lean#L407) · [Conditional exclusion](../Lean/MOC/FourContact0710HessianPencil.lean#L442) | No |
| Equal spectral branch | If $a=b$ and $t<0$, the branch polynomial gives $(a+1)^2(c+1)+e(c+1-a^2)=0$ when $d>0$. A linear combination of the Hessian rows shows that two factors of the imaginary radial gradient have the same sign. The other terms are nonnegative squares. The real radial gradient is $Q<0$, so an actual lift is impossible. The theorem also covers $d=0$. | [Row identity](../Lean/MOC/FourContact0710EqualWeights.lean#L59) · [Equal-weight exclusion](../Lean/MOC/FourContact0710EqualWeights.lean#L126) | No |

The unequal branch requires a nonpositive second difference for actual
spectra. A paper argument uses the positive and negative directions
of the Hessian and the radial form. The necessary spectral sign and
the support inequality for positive signed height remain open in Lean.
[Hessian sign argument](https://github.com/ascendnoosphere/MOC/blob/a49606d39e8bb5903c9bb4a51651a18679499c0c/Docs/research/eight0710_full_closure.txt)

[Lean check status](README.md#lean-check-status): **Partial (3/5)** for the 5 linked source modules.
