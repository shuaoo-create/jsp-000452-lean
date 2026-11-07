import IndependentLayerPrice
import ZhaoFamilyBudget
import ZhaoFourComplement
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
theorem independent_triple_vertex_set (Q : SimpleGraph X) (large : ¬NoIndependentTriple Q) :
    ∃ S : Set X, S.ncard=3 ∧ Q.IsIndepSet S := by
  classical
  unfold NoIndependentTriple at large
  push Not at large
  obtain ⟨a,b,c,ab,ac,bc,nab,nac,nbc⟩ := large
  refine ⟨{a,b,c},?_,?_⟩
  · rw [Set.ncard_insert_of_notMem (by simp [ab,ac]),Set.ncard_pair bc]
  · intro x hx y hy diff edge
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;> first
      | exact diff rfl
      | exact nab edge | exact nac edge | exact nbc edge
      | exact nab edge.symm | exact nac edge.symm | exact nbc edge.symm

theorem zhao_family_base_given_critical (d : ℕ) (hd : 2≤d)
    (crit : PerfectAfterEveryDeletion (zhaoGraph d)) : 2*d-2 ≤ baseReserve (zhaoGraph d) (2*d) := by
  have size := zhao_left_ncard d
  have nemp : (Set.range (@zhaoLeft d)).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have pay := independent_layer_two_vertex_certificate _ (2*d) (by omega) (zhao_regular d) crit _
    nemp (zhao_left_independent d) (zhao_family_budget d hd)
  rwa [size] at pay

theorem zhao_four_complement_base_given_critical (crit : PerfectAfterEveryDeletion (zhaoGraph 2)ᶜ) :
    1 ≤ baseReserve (zhaoGraph 2)ᶜ 4 := by
  obtain ⟨reg,big,cheap⟩ := zhao_four_complement_certificate
  obtain ⟨S,card,ind⟩ := independent_triple_vertex_set _ big
  have pay := independent_layer_two_vertex_certificate _ 4 (by decide) reg crit S
    (Set.nonempty_of_ncard_ne_zero (by omega)) ind cheap
  omega

#print axioms independent_triple_vertex_set
#print axioms zhao_family_base_given_critical
#print axioms zhao_four_complement_base_given_critical
end JSP452Audit.StarHost
