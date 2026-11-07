import FourBlocksPayTheLastDegreeSixExit
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u
open scoped Classical

noncomputable def uniformColourError {X:Type u} [Finite X] (G R:SimpleGraph X) (a b:ℕ) : ℕ :=
  ∑ᶠx:X,((R.neighborSet x).ncard-a+(((G \ R).neighborSet x).ncard-b))

theorem uniform_error_eq_spec {X:Type u} [Fintype X] (G R:SimpleGraph X)
    (a b:ℕ) (sub:R≤G) : uniformColourError G R a b=(uniformCaps G a b).colorGap R := by
  classical
  rw [uniformColourError,finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro x _
  have palette := palette_neighbor_sum G R sub x
  rw [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
  change _=(R.neighborSet x).ncard-a+((G.neighborSet x).ncard-(R.neighborSet x).ncard-b)
  omega

theorem every_uniform_cut_le_error {X:Type u} [Finite X] (G R:SimpleGraph X) (a b:ℕ)
    (cap:∀x,Nat.card (G.neighborSet x)≤a+b) (sub:R≤G) (S T:Set X) (dis:Disjoint S T) :
    originalFactorCut G a b S T≤(uniformColourError G R a b:ℤ) := by
  classical
  let _ := Fintype.ofFinite X
  let P := uniformCaps G a b
  have bounds (x) : P.G.degree x≤P.A x+P.B x := by
    change G.degree x≤a+b
    rw [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card];exact cap x
  have lower := P.cutDeficit_le_minColorGap dis bounds
  have fee : P.minColorGap≤P.colorGap R := Nat.sInf_le (show P.colorGap R∈{k:ℕ|∃L:SimpleGraph X,L≤P.G ∧ P.colorGap L=k} from ⟨R,sub,rfl⟩)
  rw [uniform_error_eq_spec G R a b sub]
  change P.cutDeficit S T≤(P.colorGap R:ℤ);omega

theorem uniform_cut_colour_witness {X:Type u} [Finite X] (G:SimpleGraph X) (a b:ℕ)
    (cap:∀x,Nat.card (G.neighborSet x)≤a+b) :
    ∃(R:SimpleGraph X) (S T:Set X),R≤G ∧ Disjoint S T ∧ originalFactorCut G a b S T=(uniformColourError G R a b:ℤ) := by
  classical
  let _ := Fintype.ofFinite X
  let P := uniformCaps G a b
  have bounds (x) : P.G.degree x≤P.A x+P.B x := by
    change G.degree x≤a+b
    rw [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card];exact cap x
  obtain ⟨R,S,T,sub,dis,gap,_,_⟩ := P.factor_witnesses bounds
  refine ⟨R,S,T,sub,dis,?_⟩
  rw [uniform_error_eq_spec G R a b sub]
  exact gap.symm

theorem uniform_colour_error_on_sum {X Y:Type u} [Finite X] [Finite Y] (G R:SimpleGraph X) (H B:SimpleGraph Y)
    (a b:ℕ) (red:R≤G) (blue:B≤H) :
    uniformColourError (G⊕g H) (R⊕g B) a b=uniformColourError G R a b+uniformColourError H B a b := by
  classical
  let _ := Fintype.ofFinite X
  let _ := Fintype.ofFinite Y
  have palette := (JSP452Audit.StarHost.sum_colors red blue).2
  simp only [uniformColourError,finsum_eq_sum_of_fintype,palette,Fintype.sum_sum_type,
    neighborSet_sum_inl,neighborSet_sum_inr,Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]
#print axioms every_uniform_cut_le_error
#print axioms uniform_cut_colour_witness
#print axioms uniform_colour_error_on_sum
end JSP452Audit.StarHost
