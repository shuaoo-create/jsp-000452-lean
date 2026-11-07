import SmallComplementFacts
import TriangleRegularOrder
import TripleRemovalConnected
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Direct order bound for the triangle-free regular complement. The proof
uses a degree sum and two disjoint neighborhoods, with no extremal theorem. -/
theorem regular_small_complement_data (Q : SimpleGraph X) (D : ℕ) (large : 3≤D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (small : NoIndependentTriple Q) {v w : X} (vw : Qᶜ.Adj v w) :
    let c := Nat.card X-1-D
    2≤c ∧ 2*c+3≤Nat.card X ∧ PerfectAfterEveryDeletion (Q.induce ({v,w}:Set X)ᶜ) := by
  classical
  intro c
  have order := factorCritical_order_rank Q crit v
  have odd : Odd (Nat.card X) := ⟨matchingEdges Q,by omega⟩
  have regC : ∀x,Nat.card (Qᶜ.neighborSet x)=c := complement_regular_size Q D reg
  have present : (Qᶜ.neighborSet v).Nonempty := ⟨w,vw⟩
  have pos := (Set.ncard_pos (Qᶜ.neighborSet v).toFinite).mpr present
  rw [← Nat.card_coe_set_eq,regC] at pos
  obtain ⟨k,even⟩ := regular_even_on_odd (Qᶜ) c odd regC
  have two : 2 ≤ c := by omega
  have cod : 3≤Nat.card X-1-c := by dsimp [c] at *; omega
  have size := triangle_regular_order (Qᶜ) c odd regC (complement_no_triangle Q small) two cod
  refine ⟨two,size,pair_cut_critical_of_triple_preconnected Q _ (Set.ncard_pair vw.ne) odd small ?_⟩
  exact triple_deleted_preconnected Q c regC two size small

omit [Finite X] in
theorem independent_pair_of_complement_adj (Q : SimpleGraph X) {v w : X} (vw : Qᶜ.Adj v w) :
    Q.IsIndepSet ({v,w}:Set X) := by
  obtain ⟨_,missing⟩ := (Q.compl_adj _ _).mp vw
  intro x hx y hy diff
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
  · exact False.elim (diff rfl)
  · exact missing
  · exact fun e => missing e.symm
  · exact False.elim (diff rfl)

#print axioms regular_small_complement_data
#print axioms independent_pair_of_complement_adj
end JSP452Audit.StarHost
