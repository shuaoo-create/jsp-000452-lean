import SeededFullDegreeStage
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem all_neighbors_at_residual_cap {X:Type*} [Finite X] (G H:SimpleGraph X) (sub:H≤G) (D:ℕ) (x:X)
    (cap:Nat.card (G.neighborSet x)≤D) (full:Nat.card (H.neighborSet x)=D) :
    H.neighborSet x=G.neighborSet x :=
  Set.eq_of_subset_of_ncard_le (fun _ e => sub e) (cap.trans_eq full.symm)

theorem strict_seven_stage_short (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) (K:DegreeRegion F.G 7) (p:↥K.positive)
    (B:Set F.X) (stage:CompleteDegreeStage (F.G \ wholePiece F.G K.barrier p.val) 7 B) :
    B.ncard<K.pieceCapacity p-(F.r+1) := by
  classical
  by_contra! enough
  let t := K.pieceCapacity p-(F.r+1)
  obtain ⟨U,sub,size⟩ := Set.exists_subset_card_eq (show t≤B.ncard from enough)
  let P := wholePiece F.G K.barrier p.val
  let H := F.G \ P
  obtain ⟨_,_,_,degree,_,_⟩ := minimal_rank_exact_source F paid
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤7 := (degree x).trans_eq seven
  have same (x) (hx:x∈U) : H.neighborSet x=F.G.neighborSet x :=
    all_neighbors_at_residual_cap F.G H sdiff_le 7 x (cap x) (stage.2.1 x (sub hx))
  have ind : F.G.IsIndepSet U := by
    intro x hx y hy ne edge
    have saved : y∈H.neighborSet x := (same x hx).symm ▸ edge
    exact stage.1 (sub hx) (sub hy) ne saved
  have full (x) (hx:x∈U) : Nat.card (F.G.neighborSet x)=7 := by rw [←same x hx];exact stage.2.1 x (sub hx)
  have away : ∀c∈({p}:Finset _),∀⦃x y:F.X⦄,(wholePiece F.G K.barrier c.val).Adj x y → x∉U := by
    intro c hc x y edge hx
    have cp := Finset.mem_singleton.mp hc
    subst c
    have original := wholePiece_le F.G K.barrier p.val edge
    have old : y∈F.G.neighborSet x := original
    have saved : y∈H.neighborSet x := (same x hx).symm ▸ old
    exact saved.2 edge
  have small : ∀c∈({p}:Finset _),K.pieceCapacity c≤F.r+U.ncard+1 := by
    intro c hc;rw [Finset.mem_singleton.mp hc,size];dsimp [t];omega
  have bounds := K.positive_piece_bounds cap p
  have nonzero : 0<U.ncard+∑c∈({p}:Finset _),K.pieceCapacity c := by simp only [Finset.sum_singleton];omega
  have gain := strict_piece_menu_weight F paid 7 (by omega) K {p} U ind full away small nonzero
  rw [Finset.sum_singleton,(strict_seven_original_peak F paid seven).1] at gain
  omega

theorem seven_minimum_capacity_at_least_seventeen (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) (K:DegreeRegion F.G 7) (p:↥K.positive)
    (smallest:∀q:↥K.positive,K.pieceCapacity p≤K.pieceCapacity q) :
    17≤K.pieceCapacity p := by
  obtain ⟨E,B,size,full,stage,room⟩ := strict_seven_seeded_stage F paid seven K p smallest
  have short := strict_seven_stage_short F paid seven K p B stage
  omega

#print axioms all_neighbors_at_residual_cap
#print axioms strict_seven_stage_short
#print axioms seven_minimum_capacity_at_least_seventeen
end JSP452Audit.StarHost
