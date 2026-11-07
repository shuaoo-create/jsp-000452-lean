import QuarticFullBinaryExcluded
namespace JSP452Audit.StarHost

/-- The lost multiplicity at each height is attained by an actual
feasible index set. This counts varying patterns only for the proof of
a bound at one threshold. -/
theorem threshold_removal_witness {s : ℕ} (n : Fin s→ℕ) (hn : Antitone n) (W : RemovalBudget s) (h : ℕ) :
    ∃T:↥W.choices,originalThresholdCount n h≤originalThresholdCount (W.entries n) h+
      (T.val.filter (fun z => h≤n z)).card := by
  classical
  let v := originalThresholdCount (W.entries n) h
  have upper : v≤W.len := original_threshold_le_length _ _
  have partition (T:Finset (Fin s)) : originalThresholdCount n h=
        (T.filter (fun z => h≤n z)).card+(Tᶜ.filter (fun z => h≤n z)).card := by
    let X := T.filter (fun z => h≤n z)
    let Y := Tᶜ.filter (fun z => h≤n z)
    have dis : Disjoint X Y := Finset.disjoint_left.mpr (by
      intro z a b;exact (Finset.mem_compl.mp (Finset.mem_filter.mp b).1) (Finset.mem_filter.mp a).1)
    have eq : X∪Y=Finset.univ.filter (fun z => h≤n z) := by
      ext z;simp [X,Y];tauto
    change _=X.card+Y.card
    rw [←Finset.card_union_of_disjoint dis,eq];rfl
  by_cases shorter : v<W.len
  · let i : Fin W.len := ⟨v,shorter⟩
    have low : W.entries n i<h := by
      by_contra! high
      have no := (original_threshold_prefix (W.entries n) (W.entries_antitone n hn) h i).1 high
      exact (Nat.lt_irrefl v) no
    have member : W.entries n i∈W.choices.attach.image (fun T => n (W.label T i)) := Finset.min'_mem _ _
    obtain ⟨T,_,att⟩ := Finset.mem_image.mp member
    let C := T.valᶜ
    let B := C.filter (fun z => h≤n z)
    let e := C.orderIsoOfFin rfl
    have count : B.card≤v := by
      let idx (z:↥B) := e.symm ⟨z.val,(Finset.mem_filter.mp z.property).1⟩
      have earlier (z:↥B) : (idx z).val<v := by
        by_contra! later
        let p : Fin C.card := ⟨v,shorter.trans_le (W.enough T)⟩
        have le : p ≤ idx z := later
        have sl := e.monotone le
        have same : (e (idx z)).val=z.val := congrArg Subtype.val (e.apply_symm_apply _)
        have eq : (e p).val=W.label T i := rfl
        change (e p).val≤(e (idx z)).val at sl
        rw [same,eq] at sl
        have hi := (Finset.mem_filter.mp z.property).2
        have priced := hn sl;omega
      let f (z:↥B) : Fin v := ⟨(idx z).val,earlier z⟩
      have inj : Function.Injective f := by
        intro x y same
        have ranks : idx x=idx y := Fin.ext (congrArg (fun z:Fin v => z.val) same)
        exact Subtype.ext (congrArg (fun z:↥C => z.val) (e.symm.injective ranks))
      simpa using Fintype.card_le_of_injective f inj
    have split := partition T.val
    change originalThresholdCount n h=(T.val.filter (fun z => h≤n z)).card+B.card at split
    exact ⟨T,by change _≤v+_;omega⟩
  · obtain ⟨T,mem,att⟩ := Finset.exists_mem_eq_sup W.choices W.present Finset.card
    change W.loss=T.card at att
    have size : Tᶜ.card=W.len := by rw [Finset.card_compl,Fintype.card_fin,←att];rfl
    have sub := Finset.card_le_card (Finset.filter_subset (fun z => h≤n z) Tᶜ)
    have split := partition T
    exact ⟨⟨T,mem⟩,by change _≤v+(T.filter _).card;omega⟩

#print axioms threshold_removal_witness
end JSP452Audit.StarHost
