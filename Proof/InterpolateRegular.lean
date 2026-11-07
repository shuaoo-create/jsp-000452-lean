import DirectedFactorLayer
import OrientDifference
import FactorFromSelection

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A real spanning subgraph, with all original vertices and exactly the
    indicated degree at every vertex. -/
def HasFactor {X : Type*} (H : SimpleGraph X) (a : ℕ) : Prop :=
  ∃ F : SimpleGraph X, F ≤ H ∧ ∀ v, Nat.card (F.neighborSet v) = a

theorem factor_step_two {X : Type*} [Finite X] (H : SimpleGraph X) (a k : ℕ)
    (pos : 0<k) (lower : HasFactor H a) (upper : HasFactor H (a+2*k)) :
    HasFactor H (a+2) := by
  obtain ⟨F0,sub0,lo⟩ := lower
  obtain ⟨F1,sub1,hi⟩ := upper
  obtain ⟨o⟩ := exists_difference_orientation F0 F1 a k lo hi
  obtain ⟨O,N,src,dst⟩ := directed_factor_layer o.srcO o.dstO o.srcN o.dstN k pos o.src_gap o.dst_gap
  exact ⟨_,factor_from_selection sub0 sub1 a lo o.srcO o.dstO o.srcN o.dstN o.edgeO o.edgeN O N src dst⟩

/-- Interpolate actual constant-degree factors, at all interior degrees of
    the same parity. The two endpoint subgraphs may overlap arbitrarily. -/
theorem factor_interpolation {X : Type*} [Finite X] (H : SimpleGraph X) (a j k : ℕ)
    (order : j≤k) (lower : HasFactor H a) (upper : HasFactor H (a+2*k)) :
    HasFactor H (a+2*j) := by
  induction j generalizing a k with
  | zero => simpa using lower
  | succ j ih =>
    have step := factor_step_two H a k (by omega) lower upper
    have same : (a+2)+2*(k-1) = a+2*k := by omega
    have h := ih (a:=a+2) (k:=k-1) (by omega) step (same.symm ▸ upper)
    rwa [show a+2+2*j = a+2*(j+1) by omega] at h

#print axioms factor_step_two
#print axioms factor_interpolation
end JSP452Audit.StarHost
