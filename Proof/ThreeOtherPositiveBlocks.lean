import IndependentSupplyAcrossOddBlocks
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem three_other_seven_blocks (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) (K:DegreeRegion F.G 7) (p:↥K.positive)
    (smallest:∀q:↥K.positive,K.pieceCapacity p≤K.pieceCapacity q) :
    let P := wholePiece F.G K.barrier p.val
    let H := F.G \ P
    ∃E J:Set F.X,6*K.pieceCapacity p+3≤E.ncard ∧
      (∀x∈E,Nat.card (H.neighborSet x)=7) ∧ J⊆E ∧ H.IsIndepSet J ∧
      E.ncard≤7*J.ncard ∧ Disjoint E (wholeLabels F.G K.barrier p.val) := by
  classical
  intro P H
  let T := Subtype.val '' (({p}:Set ↥K.positive)ᶜ)
  let _ := Fintype.ofFinite T
  let E := regionCore F.G K.barrier T
  let B := F.G.induce K.barrierᶜ
  obtain ⟨_,_,_,degree,_,_⟩ := minimal_rank_exact_source F paid
  have cap (v:F.X) : Nat.card (F.G.neighborSet v)≤7 := (degree v).trans_eq seven
  have count := (strict_seven_four_positive_pieces F paid seven K).1
  have three : Fintype.card T=3 := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    dsimp [T]
    rw [Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_compl,Set.ncard_singleton]
    change K.positive.ncard-1=3
    rw [count]
  have full : T⊆{c|allFullComponent F.G K.barrier 7 c} := by
    rintro _ ⟨q,_,rfl⟩;exact K.full q.property.1
  have apart : Disjoint E (wholeLabels F.G K.barrier p.val) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,rfl,hit⟩ ⟨y,hy,eq⟩
    have same : y=x := Subtype.ext eq
    subst y
    have label : B.connectedComponentMk x=p.val := hy
    obtain ⟨q,ne,tag⟩ := hit
    exact ne (Set.mem_singleton_iff.mpr (Subtype.ext (tag.trans label)))
  have remain (v) (hv:v∈E) : Nat.card (H.neighborSet v)=7 := by
    have away : ∀⦃x y⦄,P.Adj x y → x∉E := fun _ _ edge he => Set.disjoint_left.mp apart he edge.2.1
    rw [show H.neighborSet v=F.G.neighborSet v from neighborSet_after_disjoint_piece F.G P E away hv]
    exact regionCore_full_degree F.G K.barrier T 7 full hv
  have order (c:↥T) : Odd (Nat.card c.val.supp) ∧ 2*K.pieceCapacity p+1≤Nat.card c.val.supp := by
    obtain ⟨q,_,eq⟩ := c.property
    have exactSize := factorCritical_order_rank q.val.toSimpleGraph (K.critical q.val).2 q.val.nonempty_supp.to_subtype.some
    change Nat.card q.val.supp=2*K.pieceCapacity q+1 at exactSize
    rw [←eq,exactSize]
    exact ⟨⟨K.pieceCapacity q,rfl⟩,by have := smallest q;omega⟩
  obtain ⟨I,inside,ind,room⟩ := odd_component_union_independent_supply B 7
    (fun v => (induced_neighbor_count_le F.G K.barrierᶜ v).trans (cap v.val)) T
    (by decide) (fun c => (order c).1)
  let J := Subtype.val '' I
  have card : J.ncard=I.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have sizes := core_order_sum F.G K.barrier T
  change E.ncard=_ at sizes
  have lo := Finset.sum_le_sum (s:=Finset.univ) (fun (c:↥T) _ => (order c).2)
  rw [Finset.sum_const,Finset.card_univ,three,nsmul_eq_mul,Nat.cast_id,←sizes] at lo
  refine ⟨E,J,by omega,remain,?_,?_,?_,apart⟩
  · rintro _ ⟨v,hv,rfl⟩;exact ⟨v,rfl,inside v hv⟩
  · rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne edge
    exact ind hv hw (fun eq => ne (congrArg Subtype.val eq)) edge.1
  · rw [sizes,card];exact room

#print axioms three_other_seven_blocks
end JSP452Audit.StarHost
