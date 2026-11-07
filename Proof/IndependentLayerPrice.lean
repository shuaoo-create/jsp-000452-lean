import RegularIndependentReserve
import EquimatchableReserve
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- An independent set pays against any single real deletion layer below
the top. The deletion witness may use a different set of vertices. -/
theorem independent_layer_lower (Q : SimpleGraph X) (d : ℕ)
    (reg : ∀x,Nat.card (Q.neighborSet x)=d+1) (crit : PerfectAfterEveryDeletion Q)
    (I : Set X) (nonempty : I.Nonempty) (indep : Q.IsIndepSet I)
    (j : ℕ) (below : j<d) :
    I.ncard + deletionBudget (Q.induce Iᶜ) (j+1) ≤ baseReserve Q (d+1) + deletionBudget Q (j+1) := by
  have sum := regular_independent_reserve Q d reg crit I nonempty indep
  have has : j ∈ Finset.range d := Finset.mem_range.mpr below
  have one : savedAt Q I (j+1) ≤ ∑ k∈Finset.range d,savedAt Q I (k+1) :=
    Finset.single_le_sum (f:=fun k => savedAt Q I (k+1)) (fun _ _ => Nat.zero_le _) has
  have eq : savedAt Q I (j+1)+deletionBudget Q (j+1) =
      I.ncard+deletionBudget (Q.induce Iᶜ) (j+1) :=
    Nat.sub_add_cancel (deletion_le_after_cut_add Q I _)
  dsimp only at sum
  omega

theorem independent_layer_two_vertex_certificate (Q : SimpleGraph X) (D : ℕ) (large : 2≤D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (I : Set X) (nonempty : I.Nonempty) (indep : Q.IsIndepSet I)
    (cheap : deletionBudget Q (D-1)≤2) :
    I.ncard-2 ≤ baseReserve Q D := by
  have h1 : D-1+1=D := by omega
  have h2 : D-2+1=D-1 := by omega
  have price := independent_layer_lower Q (D-1) (by simpa [h1] using reg) crit I nonempty indep (D-2) (by omega)
  rw [h1,h2] at price
  omega
#print axioms independent_layer_two_vertex_certificate
end JSP452Audit.StarHost
