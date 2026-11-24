# Status of Zheng’s order-four claim

[Zheng’s preprint](https://doi.org/10.13140/RG.2.2.36790.25923) reports the full order-four theorem. The separate exceptional-contact supplement was not available to this review. This repository neither verifies the full theorem in Lean nor refutes it.

The structural real-orthogonal restriction is proved in [FourMinorTransport.lean](MOC/FourMinorTransport.lean). The conditions on actual separating witnesses are in [StationaryFour.lean](MOC/Reformulations/StationaryFour.lean). An actual strict witness refutes MOC; the converse step to the specific stationary chamber is not a theorem in this library.
