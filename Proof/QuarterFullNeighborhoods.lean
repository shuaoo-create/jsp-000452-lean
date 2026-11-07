import ExteriorIndependentPrice
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- A concrete dominating set for just the remaining full vertices T inside
Y. Only their actual edges out of Y enter the cost. -/
theorem dominate_full_inside_at_quarter (G : SimpleGraph X) (Y B T : Set X)
    (apart : Disjoint Y B) (cover : Y∪B=Set.univ) (sub : T⊆Y)
    (D : ℕ) (pos : 0<D) (full : ∀v∈T,Nat.card (G.neighborSet v)=D) :
    ∃S:Set X,S⊆Y ∧ (∀v∈T,v∈S ∨ ∃w∈S,G.Adj v w) ∧
      ((D:ℚ)-1)*S.ncard≤((D:ℚ)-1)*(1/4+(3/4:ℚ)^(D+1))*Y.ncard+crossCount G T B := by
  classical
  let _ := Fintype.ofFinite Y
  let _ := Fintype.ofFinite T
  let N (t:T) : Set Y := {v | v.val=t.val ∨ G.Adj t.val v.val}
  let b (t:T) := (G.neighborSet t.val∩B).ncard
  have nonempty (t:T) : (N t).Nonempty := ⟨⟨t.val,sub t.property⟩,Or.inl rfl⟩
  have domain (t:T) : (N t).ncard+b t=D+1 := by
    let L := G.neighborSet t.val
    have image : Subtype.val '' N t=insert t.val (L∩Y) := by
      ext v
      constructor
      · rintro ⟨v,h,rfl⟩
        rcases h with eq|adj
        · exact Or.inl eq
        · exact Or.inr ⟨adj,v.property⟩
      · rintro (eq|h)
        · exact ⟨⟨v,eq.symm ▸ sub t.property⟩,Or.inl eq,rfl⟩
        · exact ⟨⟨v,h.2⟩,Or.inr h.1,rfl⟩
    have card := (Set.ncard_image_of_injective (N t) Subtype.val_injective).symm.trans (congrArg Set.ncard image)
    rw [Set.ncard_insert_of_notMem (fun h => G.irrefl (show G.Adj t.val t.val from h.1))] at card
    have partition : (L∩Y)∪(L∩B)=L := by rw [←Set.inter_union_distrib_left,cover,Set.inter_univ]
    have sum := congrArg Set.ncard partition
    rw [Set.ncard_union_eq (apart.mono Set.inter_subset_right Set.inter_subset_right),
      ←Nat.card_coe_set_eq (s:=L),show Nat.card L=D from full t.val t.property] at sum
    change (N t).ncard+(L∩B).ncard=D+1
    omega
  obtain ⟨S,hit,bound⟩ := quarter_sample_transversal N nonempty
  let U := Subtype.val '' S
  have cost : ∑t:T,b t=crossCount G T B := (crossCount_eq_neighbor_sum G T B).symm
  have term (t:T) : ((D:ℚ)-1)*(3/4:ℚ)^(N t).ncard≤((D:ℚ)-1)*(3/4:ℚ)^(D+1)+b t := by
    have sz := domain t
    have cap : b t≤D := by
      exact (Set.ncard_le_ncard Set.inter_subset_left).trans ((Nat.card_coe_set_eq _).symm.le.trans (full _ t.property).le)
    have localI := missed_with_exterior_charge D (b t) cap
    rw [show D+1-b t=(N t).ncard by omega] at localI;exact localI
  have sum := Finset.sum_le_sum (s:=(Finset.univ : Finset T)) (fun t _ => term t)
  have bq : (∑t:T,(b t:ℚ))=(crossCount G T B:ℚ) := by exact_mod_cast cost
  rw [Finset.sum_add_distrib,bq,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq,nsmul_eq_mul] at sum
  have num : (T.ncard:ℚ)≤Y.ncard := by exact_mod_cast Set.ncard_le_ncard sub
  have positive : 0≤(D:ℚ)-1 := by apply sub_nonneg.mpr;exact_mod_cast (show 1≤D from pos)
  have cmp := mul_le_mul_of_nonneg_right num (show 0≤((D:ℚ)-1)*(3/4:ℚ)^(D+1) by positivity)
  have scale := mul_le_mul_of_nonneg_left bound positive
  rw [Nat.card_coe_set_eq Y] at scale
  have span : U.ncard=S.ncard := Set.ncard_image_of_injective S Subtype.val_injective
  refine ⟨U,?_,?_,?_⟩
  · rintro _ ⟨v,_,rfl⟩;exact v.property
  · intro v hv
    obtain ⟨w,ws,h⟩ := hit (⟨v,hv⟩:T)
    rcases h with e|edge
    · exact Or.inl ⟨w,ws,e⟩
    · exact Or.inr ⟨w.val,⟨w,ws,rfl⟩,edge⟩
  · rw [span];nlinarith

#print axioms dominate_full_inside_at_quarter
end JSP452Audit.StarHost
