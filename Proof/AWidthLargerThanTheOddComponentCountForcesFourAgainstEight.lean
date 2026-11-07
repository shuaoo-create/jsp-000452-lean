import RemovingTheOnlyOddRegularComponent
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_excess_width_forces_four_eight (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (excess:(oddRegularComponents F.G 10).ncard<highestWidth F.n F.m F.r) :
    (0<originalThresholdCount F.n 8 ∨ 0<originalThresholdCount F.m 8) ∧
    ∃u v:ℕ,0<u ∧ 0<v ∧ u+v-1=highestWidth F.n F.m F.r ∧
      Forces F.G (forest (fun _:Fin u => 4)) (forest (fun _:Fin v => 8)) := by
  obtain ⟨i,j,u,v,_,wide,shape,pos,live,force,_⟩ := strict_ten_true_factor_peak F paid ten
  rcases shape with ⟨r,b⟩|⟨r,b⟩|⟨r,b⟩ <;> rw [r,b] at force
  · have tip := (original_threshold_prefix F.m F.hm 8 j).mp b.ge
    exact ⟨Or.inr (by omega),u,v,pos,live,wide,force⟩
  · have tip := (original_threshold_prefix F.n F.hn 8 i).mp r.ge
    exact ⟨Or.inl (by omega),v,u,live,pos,by omega,forces_swap force⟩
  · have cap (x:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
    obtain ⟨S,T,dis,bill⟩ := original_uniform_factor_cut F.G 6 6 u v (by decide) (by decide) pos live cap force
    have mid := balanced_cut_le_original_odd_regular F.G 5 cap S T dis
    change originalFactorCut F.G 5 5 S T≤((oddRegularComponents F.G 10).ncard:ℤ) at mid
    change (u+v-1:ℕ)≤originalFactorCut F.G 5 5 S T at bill
    omega

theorem two_summands_force_error_two {X Y:Type u} [Finite X] [Finite Y] (C:SimpleGraph X) (O:SimpleGraph Y)
    (capC:∀x,Nat.card (C.neighborSet x)≤10) (capO:∀x,Nat.card (O.neighborSet x)≤10)
    (u v:ℕ) (hu:0<u) (hv:0<v) (width:u+v-1=2)
    (force:Forces (C⊕g O) (forest (fun _:Fin u => 4)) (forest (fun _:Fin v => 8)))
    (R:SimpleGraph X) (B:SimpleGraph Y) (subC:R≤C) (subO:B≤O) :
    2≤uniformColourError C R 3 7+uniformColourError O B 3 7 := by
  have cap (w:X⊕Y) : Nat.card ((C⊕g O).neighborSet w)≤10 := by
    rcases w with x|y
    · rw [Nat.card_coe_set_eq,neighborSet_sum_inl,Set.ncard_image_of_injective _ Sum.inl_injective];exact capC x
    · rw [Nat.card_coe_set_eq,neighborSet_sum_inr,Set.ncard_image_of_injective _ Sum.inr_injective];exact capO y
  obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut (C⊕g O) 4 8 u v (by decide) (by decide) hu hv cap force
  have paid := every_uniform_cut_le_error (C⊕g O) (R⊕g B) 3 7 cap (fun {x y} => by
    rcases x with x|x <;> rcases y with y|y
    · intro edge;exact subC edge
    · intro e;exact (not_adj_sum_inl_inr _ _ e).elim
    · intro e;exact (not_adj_sum_inl_inr _ _ e.symm).elim
    · intro edge;exact subO edge) S T dis
  rw [uniform_colour_error_on_sum C R O B 3 7 subC subO] at paid
  change (u+v-1:ℕ)≤originalFactorCut (C⊕g O) 3 7 S T at fee
  omega
#print axioms ten_excess_width_forces_four_eight
#print axioms two_summands_force_error_two
end JSP452Audit.StarHost
