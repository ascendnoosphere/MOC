import MOC.Core

namespace MOC

/-- The unrestricted Marcus–de Oliveira conjecture in every finite order.
This proposition is the open target for the spectral formulation. -/
def MOCIsTrue : Prop :=
  ∀ n : ℕ, Conjecture (Fin n)

end MOC
