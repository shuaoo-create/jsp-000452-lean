import SingleExtraLabelCounts
namespace JSP452Audit.StarHost.PairedLayers
open SimpleGraph

theorem all_label_layers {X A:Type*} [Finite X] [Finite A] (k:ℕ) (Q:SimpleGraph X) (t:A→X)
    (cap:∀v,Nat.card (Q.neighborSet v)+Nat.card {a:A // t a=v}≤2*(k+1)) :
    ∃V:TwoDegreeLayers Q (k+1),∃owner:A→Fin (k+1),
      (Finset.univ.filter (fun j => Odd (({a:A|owner a=j}:Set _).ncard))).card≤1 ∧
      (∀j v,((V.part j).neighborSet v).ncard+({a:A|owner a=j ∧ t a=v}:Set _).ncard≤2) := by
  classical
  by_cases ev:Even (Nat.card A)
  · obtain ⟨V,c,par,paid⟩ := even_label_layers k Q t ev cap
    refine ⟨V,c,?_,paid⟩
    have empty : Finset.univ.filter (fun j => Odd (({a:A|c a=j}:Set _).ncard))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j h;exact (Nat.not_even_iff_odd.mpr (Finset.mem_filter.mp h).2) (par j)
    simp [empty]
  · obtain ⟨n,h⟩ := Nat.not_even_iff_odd.mp ev
    have padded : Even (Nat.card (A⊕Unit)) := by
      rw [Nat.card_sum];simp only [Nat.card_unique];exact ⟨n+1,by omega⟩
    let H := Q ⊕g (⊥:SimpleGraph Unit)
    obtain ⟨V,c,par,paid⟩ := even_label_layers k H (paddedTip t) padded (padded_port_budget k Q t cap)
    let emb : X↪X⊕Unit := ⟨Sum.inl,Sum.inl_injective⟩
    let U : TwoDegreeLayers Q (k+1) := V.restrict emb
    refine ⟨U,fun a => c (.inl a),single_extra_parity c par,?_⟩
    intro j v
    have equal := sum_left_fiber_card (p:=fun a => c (.inl a)=j ∧ t a=v)
      (q:=fun z => c z=j ∧ paddedTip t z=.inl v)
      (fun _ => by simp [paddedTip]) (by simp [paddedTip])
    change ({a:A|c (.inl a)=j ∧ t a=v}:Set _).ncard=({z:A⊕Unit|c z=j ∧ paddedTip t z=.inl v}:Set _).ncard at equal
    rw [equal]
    let f (x:(U.part j).neighborSet v) : (V.part j).neighborSet (.inl v) := ⟨.inl x.val,x.property⟩
    have deg := Nat.card_le_card_of_injective f (fun _ _ e => Subtype.ext (Sum.inl.inj (congrArg Subtype.val e)))
    exact (Nat.add_le_add_right deg _).trans (paid j (.inl v))

#print axioms all_label_layers
end JSP452Audit.StarHost.PairedLayers
