import ActualMatchingPairKey
import PairedSampleTransversal
import ExteriorIndependentPrice
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem five_local_miss (k b : ℕ) (order : k+b=6) (atMost : b≤5) :
    4*(7/10:ℚ)^k≤4*(7/10:ℚ)^6+b := by
  rw [show k=6-b by omega]
  rcases (show b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 by omega) with h|h|h|h|h|h <;> rw [h] <;> norm_num

/-- The actual matched labels get a discount on full closed neighbourhoods.
All other losses are charged only to original incidences into B. -/
theorem five_dominate_with_matching (G : SimpleGraph X) (Y B T : Set X)
    (apart : Disjoint Y B) (cover : Y∪B=Set.univ) (sub : T⊆Y)
    (full : ∀v∈T,Nat.card (G.neighborSet v)=5)
    (M : (G.induce Y).Subgraph) (matchM : M.IsMatching)
    (land : ∀y∈M.verts,y.val∈T) (closed : ∀y∈M.verts,∀w∈B,¬G.Adj y.val w) :
    ∃S:Set X,S⊆Y ∧ (∀v∈T,v∈S ∨ ∃w∈S,G.Adj v w) ∧
      4*(S.ncard:ℚ)+(4/50:ℚ)*M.verts.ncard≤4*(21/50:ℚ)*Y.ncard+crossCount G T B := by
  classical
  let _ := Fintype.ofFinite Y
  let _ := Fintype.ofFinite T
  let N (t:T) : Set Y := {v | v.val=t.val ∨ G.Adj t.val v.val}
  let b (t:T) := (G.neighborSet t.val∩B).ncard
  have nonempty (t:T) : (N t).Nonempty := ⟨⟨t.val,sub t.property⟩,Or.inl rfl⟩
  have domain (t:T) : (N t).ncard+b t=6 := by
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
      ←Nat.card_coe_set_eq (s:=L),show Nat.card L=5 from full t.val t.property] at sum
    change (N t).ncard+(L∩B).ncard=6
    omega
  let y (t:T) : Y := ⟨t.val,sub t.property⟩
  let marked := {t:T | y t∈M.verts}
  have mc : marked.ncard=M.verts.ncard := by
    let f (t:↥marked) : M.verts := ⟨y t.val,t.property⟩
    have inj : Function.Injective f := fun a b eq => Subtype.ext (Subtype.ext
      (congrArg (fun z:M.verts => z.val.val) eq))
    have onto : Function.Surjective f := fun w => ⟨⟨⟨w.val.val,land _ w.property⟩,w.property⟩,rfl⟩
    exact (Nat.card_coe_set_eq _).symm.trans ((Nat.card_congr (Equiv.ofBijective f ⟨inj,onto⟩)).trans (Nat.card_coe_set_eq _))
  obtain ⟨key,paired⟩ := actual_matching_pair_key (G.induce Y) M matchM
  have pairedN (t:T) (mark:t∈marked) : ∃i,(pairSidesAt key (N t) i).card=2 := by
    obtain ⟨w,edge,id,opposite⟩ := paired (y t) mark
    exact ⟨(key (y t)).1,neighboring_pair_has_two_sides key (N t) (Or.inl rfl)
      (show w∈N t from Or.inr (M.adj_sub edge)) id opposite⟩
  obtain ⟨S,hit,bound⟩ := paired_sample_transversal key N nonempty marked pairedN
  let U := Subtype.val '' S
  let rate (t:T) : ℚ := (if t∈marked then (40/49:ℚ) else 1)*(7/10:ℚ)^(N t).ncard
  let flag (t:T) : ℚ := if t∈marked then 1 else 0
  have term (t:T) : 4*rate t+flag t*(4/50)≤4*(7/10:ℚ)^6+b t := by
    have sz := domain t
    by_cases yes:t∈marked
    · have zero : b t=0 := by
        have empty : G.neighborSet t.val∩B=∅ := Set.eq_empty_iff_forall_notMem.mpr
          (fun w h => closed (y t) yes w h.2 h.1)
        dsimp [b];rw [empty,Set.ncard_empty]
      have six : (N t).ncard=6 := by omega
      dsimp only [rate,flag];rw [if_pos yes,if_pos yes,six,zero];norm_num
    · have cap : b t≤5 := (Set.ncard_le_ncard Set.inter_subset_left).trans
          ((Nat.card_coe_set_eq _).symm.le.trans (full _ t.property).le)
      simpa [rate,flag,yes] using five_local_miss (N t).ncard (b t) sz cap
  have flags : (∑t:T,flag t)=(marked.ncard:ℚ) := by
    have nat : (∑t:T,if t∈marked then (1:ℕ) else 0)=marked.ncard := by
      rw [Finset.sum_boole]
      have eq : (Finset.univ.filter (fun t:T => t∈marked))=marked.toFinset := by ext t;simp
      rw [eq,Set.toFinset_card,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Nat.cast_id]
    dsimp only [flag];exact_mod_cast nat
  have cost : ∑t:T,b t=crossCount G T B := (crossCount_eq_neighbor_sum G T B).symm
  have bq : (∑t:T,(b t:ℚ))=(crossCount G T B:ℚ) := by exact_mod_cast cost
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun t _ => term t)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,flags,mc,
    bq,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,nsmul_eq_mul] at total
  change (S.ncard:ℚ)≤(3/10)*(Nat.card Y:ℚ)+∑t:T,rate t at bound
  rw [Nat.card_coe_set_eq] at bound
  have num : (T.ncard:ℚ)≤Y.ncard := by exact_mod_cast Set.ncard_le_ncard sub
  have span : U.ncard=S.ncard := Set.ncard_image_of_injective S Subtype.val_injective
  refine ⟨U,?_,?_,?_⟩
  · rintro _ ⟨v,_,rfl⟩;exact v.property
  · intro v hv
    obtain ⟨w,ws,h⟩ := hit (⟨v,hv⟩:T)
    rcases h with e|edge
    · exact Or.inl ⟨w,ws,e⟩
    · exact Or.inr ⟨w.val,⟨w,ws,rfl⟩,edge⟩
  · rw [span];norm_num at total ⊢;linarith

#print axioms five_dominate_with_matching
end JSP452Audit.StarHost
