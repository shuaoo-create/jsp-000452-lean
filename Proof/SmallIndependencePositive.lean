import RegularComplementData
import PairCutDegrees
import FactorCriticalReserve
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Positive base reserve in the whole noncomplete regular factor-critical
branch with independence number at most two. No classification is assumed. -/
theorem small_independence_noncomplete_reserve (Q : SimpleGraph X) (D : ℕ) (large : 3≤D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (small : NoIndependentTriple Q) (noncomplete : Q≠⊤) : 1≤baseReserve Q D := by
  obtain ⟨v,w,vw⟩ := exists_complement_edge_of_ne_top Q noncomplete
  let _ : Nonempty X := ⟨v⟩
  let c := Nat.card X-1-D
  let I : Set X := {v,w}
  let H := Q.induce Iᶜ
  obtain ⟨two,order,fc⟩ := regular_small_complement_data Q D large reg crit small vw
  obtain ⟨cap,⟨x,peak⟩,⟨y,low⟩⟩ := pair_cut_degrees Q D c reg
    (complement_regular_size Q D reg) (complement_no_triangle Q small) two order vw
  have strict := factorCritical_nonregular_reserve H fc (D-1) D cap x y peak low
  have eqD : D-1+1=D := by omega
  have balance := regular_independent_reserve Q (D-1) (by simpa [eqD] using reg) crit I
    ⟨v,Set.mem_insert _ _⟩ (independent_pair_of_complement_adj Q vw)
  change baseReserve Q (D-1+1) = baseReserve H (D-1+1)+ _ + _ at balance
  rw [eqD] at balance
  omega

#print axioms small_independence_noncomplete_reserve
end JSP452Audit.StarHost
