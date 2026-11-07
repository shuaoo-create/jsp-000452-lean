import RegionWeights
namespace JSP452Audit.StarHost
open SimpleGraph
theorem degree_sum_le_cap {X : Type*} [Finite X] (G : SimpleGraph X) (U : Set X) (D : ℕ)
    (bound : ∀ v ∈ U, Nat.card (G.neighborSet v) ≤ D) :
    originalDegreeSum G U ≤ D*U.ncard := by
  classical
  have card : U.toFinite.toFinset.card = U.ncard := by
    rw [← Set.ncard_coe_finset,U.toFinite.coe_toFinset]
  unfold originalDegreeSum
  have le := Finset.sum_le_sum (s:=U.toFinite.toFinset) (g:=fun _ => D)
    (f:=fun v => Nat.card (G.neighborSet v)) (fun v hv => bound v (U.toFinite.mem_toFinset.mp hv))
  simpa [card,Nat.mul_comm] using le

theorem degree_sum_full {X : Type*} [Finite X] (G : SimpleGraph X) (U : Set X) (D : ℕ)
    (full : ∀ v ∈ U, Nat.card (G.neighborSet v)=D) :
    originalDegreeSum G U = D*U.ncard := by
  classical
  have card : U.toFinite.toFinset.card = U.ncard := by
    rw [← Set.ncard_coe_finset,U.toFinite.coe_toFinset]
  unfold originalDegreeSum
  calc
    _ = ∑ _v ∈ U.toFinite.toFinset, D := Finset.sum_congr rfl (fun v hv => full v (U.toFinite.mem_toFinset.mp hv))
    _ = _ := by simp [card,Nat.mul_comm]
#print axioms degree_sum_full
end JSP452Audit.StarHost