import NestedBarrier
import FactorCriticalPeak

namespace JSP452Audit.StarHost
open SimpleGraph

/-- The number of odd components has the same residue mod two as the order. -/
private theorem odd_count_mod {X : Type*} [Finite X] (Q : SimpleGraph X) :
    Q.oddComponents.ncard % 2 = Nat.card X % 2 := by
  have parity := Q.odd_ncard_oddComponents
  simp only [Nat.odd_iff] at parity
  omega

/-- If no nonempty internal cut retains the parity-corrected score, then
the original graph has odd order and each of its vertex deletions has an
actual perfect matching. -/
theorem odd_critical_of_strict_nonempty_cuts {X : Type*} [Finite X] [Nonempty X]
    (Q : SimpleGraph X)
    (strict : ∀ Z : Set X, Z.Nonempty →
      (Q.induce Zᶜ).oddComponents.ncard < (if Odd (Nat.card X) then 1 else 0) + Z.ncard) :
    Odd (Nat.card X) ∧ PerfectAfterEveryDeletion Q := by
  classical
  have odd : Odd (Nat.card X) := by
    by_contra notOdd
    let v := Classical.arbitrary X
    let S : Set X := {v}
    have size : S.ncard = 1 := Set.ncard_singleton _
    have small := strict S ⟨v,rfl⟩
    rw [if_neg notOdd,size] at small
    have count := odd_count_mod (Q.induce Sᶜ)
    rw [Nat.card_coe_set_eq] at count
    have all := Set.ncard_add_ncard_compl S
    rw [size] at all
    rw [Nat.odd_iff] at notOdd
    omega
  refine ⟨odd,?_⟩
  intro v
  let S : Set X := {v}
  let Y := Q.induce Sᶜ
  change ∃ M : Y.Subgraph, M.IsPerfectMatching
  apply Y.tutte.mpr
  intro T
  rw [tutte_violator_induce]
  let Z := outerCut S T
  have hasV : Z.Nonempty := ⟨v,Or.inl rfl⟩
  have size : Z.ncard = 1 + T.ncard := by
    rw [outerCut_ncard]; exact congrArg (· + T.ncard) (Set.ncard_singleton v)
  have strictZ := strict Z hasV
  rw [if_pos odd,size] at strictZ
  have same : (Y.induce Tᶜ).oddComponents.ncard = (Q.induce Zᶜ).oddComponents.ncard :=
    odd_ncard_iso (nestedCutIso Q S T)
  have parity := odd_count_mod (Q.induce Zᶜ)
  rw [Nat.card_coe_set_eq] at parity
  have all := Set.ncard_add_ncard_compl Z
  rw [size] at all
  rw [Nat.odd_iff] at odd
  omega

#print axioms odd_critical_of_strict_nonempty_cuts
end JSP452Audit.StarHost
