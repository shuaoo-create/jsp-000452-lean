import ComponentStarLoad
namespace JSP452Audit.StarHost
open SimpleGraph
variable {I X : Type*} [Fintype I] [Finite X]

/-- In a factor-critical component of a rank-saturating forest copy there
is room for at most one extra leaf beyond one per star. Even if other
components are arbitrarily large, they cannot compensate locally. -/
theorem critical_component_star_load (G : SimpleGraph X) (n : I→ℕ) (pn : ∀i,1≤n i)
    (f : (forest n).Copy G) (tight : Fintype.card I=matchingEdges G) (c : G.ConnectedComponent)
    (crit : PerfectAfterEveryDeletion c.toSimpleGraph) :
    let A := {i | f (center n i)∈c.supp}
    (∑ᶠ i : A,(n i.val-1)) ≤ 1 ∧
      matchingEdges c.toSimpleGraph ≤ (Finset.univ.filter (fun i => n i=1)).card+1 := by
  classical
  intro A
  obtain ⟨load,space⟩ := star_load_at_matching_rank G n pn f tight c
  change A.ncard=matchingEdges c.toSimpleGraph at load
  change (∑ᶠ i : A,(n i.val+1))≤Nat.card c.supp at space
  rw [finsum_eq_sum_of_fintype] at space ⊢
  have mass (i : A) : n i.val+1=2+(n i.val-1) := by have h:=pn i.val;omega
  simp_rw [mass] at space
  rw [Finset.sum_add_distrib] at space
  have countA : Fintype.card A=matchingEdges c.toSimpleGraph := by
    rwa [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have sum2 : (∑ _ : A,(2 : ℕ))=2*matchingEdges c.toSimpleGraph := by simp [countA,Nat.mul_comm]
  have order := factorCritical_order_rank c.toSimpleGraph crit c.nonempty_supp.to_subtype.some
  change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at order
  have slack : (∑i:A,(n i.val-1))≤1 := by omega
  refine ⟨slack,?_⟩
  let units := Finset.univ.filter (fun i : A => n i.val=1)
  have account (i : A) : 1≤(if n i.val=1 then 1 else 0)+(n i.val-1) := by
    have hi := pn i.val
    split <;> omega
  have calcUnits := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => account i)
  rw [Finset.sum_add_distrib,←Finset.card_filter] at calcUnits
  change (∑ _ : A,(1 : ℕ)) ≤ units.card+∑i:A,(n i.val-1) at calcUnits
  have ones : (∑ _ : A,(1 : ℕ))=matchingEdges c.toSimpleGraph := by simp [countA]
  let big := Finset.univ.filter (fun i : I => n i=1)
  have sub : units.image Subtype.val ⊆ big := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
  have size := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at size
  change matchingEdges c.toSimpleGraph≤big.card+1
  omega

/-- Consequently two arbitrary stars versus a forest with at most two unit
(one-leaf) stars has the exact original size Ramsey number at every length. -/
theorem erdos561_two_against_few_units {t : ℕ} (ht : 0<t) (n : Fin 2→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (few : (Finset.univ.filter (fun j => m j=1)).card≤2) :
    sizeRamsey (forest n) (forest m)=∑ k∈Finset.Icc 2 (2+t),diagonal n m k := by
  by_cases single : t=1
  · exact erdos561_single_list (by decide) ht n m hn hm pn pm (by omega)
  by_contra fail
  have two : 2≤t := by omega
  obtain ⟨V,G,_,force,rank,cap,four,_,c,miss,reg,crit⟩ := two_list_fixed_component_source two n m hn hm pn pm fail
  let D := diagonal n m 2-1
  have blueCopy : (forest m).IsContained G := by
    rcases force ⊥ bot_le with red|blue
    · have bad := forest_copy_matching (⊥ : SimpleGraph (Fin V)) n pn red
      rw [Fintype.card_fin,matchingEdges_bot] at bad
      omega
    · simpa only [sdiff_bot] using blue
  obtain ⟨f⟩ := blueCopy
  have tight : Fintype.card (Fin t)=matchingEdges G := by rw [Fintype.card_fin,rank]
  have load := (critical_component_star_load G m pm f tight c crit).2
  have lower := (unpaid_component_density_obstruction G D D (by omega) cap c miss).1
  have order := factorCritical_order_rank c.toSimpleGraph crit c.nonempty_supp.to_subtype.some
  change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at order
  change D+5≤Nat.card c.supp at lower
  omega

#print axioms critical_component_star_load
#print axioms erdos561_two_against_few_units
end JSP452Audit.StarHost
