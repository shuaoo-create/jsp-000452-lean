import StarArrow
import HostTransport

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Upper inequality of the pinned Erdős #561 statement. Its hypotheses on list
    order and positivity are unnecessary for this direction. -/
theorem erdos561_upper {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) :
    sizeRamsey (forest n) (forest m) ≤
      ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  rw [← host_ncard n m]
  exact sizeRamsey_le_of_host _ _ _ (fun R _ => host_arrows n m R)

#print axioms erdos561_upper
end JSP452Audit.StarHost
