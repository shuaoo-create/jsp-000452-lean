import SmallAlphaPerfect
import RegularIndependentReserve
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

omit [Finite X] in
theorem complement_no_triangle (Q : SimpleGraph X) (small : NoIndependentTriple Q) :
    ∀x y z,Qᶜ.Adj x y → Qᶜ.Adj y z → ¬Qᶜ.Adj z x := by
  intro x y z xy yz zx
  obtain ⟨hxy,nxy⟩ := (Q.compl_adj _ _).mp xy
  obtain ⟨hyz,nyz⟩ := (Q.compl_adj _ _).mp yz
  obtain ⟨hzx,nzx⟩ := (Q.compl_adj _ _).mp zx
  exact (small x y z hxy hzx.symm hyz).elim nxy (fun h => h.elim (fun e => nzx e.symm) nyz)

theorem regular_even_on_odd (T : SimpleGraph X) (c : ℕ) (odd : Odd (Nat.card X))
    (reg : ∀x,Nat.card (T.neighborSet x)=c) : Even c := by
  classical
  let _ := Fintype.ofFinite X
  have deg : ∀x,T.degree x = c := fun x => by
    rw [← T.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,reg]
  have sum := T.sum_degrees_eq_twice_card_edges
  simp only [deg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card] at sum
  have evenProd : Even (Nat.card X*c) := ⟨T.edgeFinset.card,by rw [←two_mul]; exact sum⟩
  rcases Nat.even_mul.mp evenProd with e|e
  · have h := Nat.even_iff.mp e; have k := Nat.odd_iff.mp odd; omega
  · exact e

theorem complement_regular_size (Q : SimpleGraph X) (D : ℕ)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) :
    ∀x, Nat.card (Qᶜ.neighborSet x) = Nat.card X-1-D := by
  classical
  let _ := Fintype.ofFinite X
  intro x
  simpa only [← Qᶜ.card_neighborSet_eq_degree,← Q.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card,reg] using Q.degree_compl x

theorem pair_cut_critical_of_triple_preconnected (Q : SimpleGraph X) (S : Set X)
    (size : S.ncard=2) (odd : Odd (Nat.card X)) (small : NoIndependentTriple Q)
    (conn : ∀T : Set X,T.ncard=3 → (Q.induce Tᶜ).Preconnected) :
    PerfectAfterEveryDeletion (Q.induce Sᶜ) := by
  have card := Set.ncard_add_ncard_compl S
  have parity := Nat.odd_iff.mp odd
  apply critical_of_odd_small_alpha _ (by rw [Nat.odd_iff,Nat.card_coe_set_eq]; omega) (small.induce _)
  · intro v
    change ((Q.induce Sᶜ).induce ({v} : Set ↥(Sᶜ : Set X))ᶜ).Preconnected
    apply (nestedCutIso Q S {v}).preconnected_iff.mpr
    apply conn
    rw [outerCut_ncard,Set.ncard_singleton,size]

#print axioms complement_no_triangle
#print axioms regular_even_on_odd
#print axioms complement_regular_size
#print axioms pair_cut_critical_of_triple_preconnected
end JSP452Audit.StarHost
