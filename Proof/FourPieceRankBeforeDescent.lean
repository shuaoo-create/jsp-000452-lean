import TwoHighestColumnsAtGeneralCap
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem four_minimum_blocks_fit_matching (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) (K:DegreeRegion F.G 7) (p:↥K.positive)
    (small:∀q:↥K.positive,K.pieceCapacity p≤K.pieceCapacity q) :
    4*K.pieceCapacity p≤matchingEdges F.G := by
  classical
  let _ := Fintype.ofFinite ↥K.positive
  let e := Function.Embedding.subtype (·∈K.positive)
  let P := (Finset.univ:Finset ↥K.positive).sup (fun i => wholePiece F.G K.barrier (e i))
  have sub : P≤F.G := Finset.sup_le (fun i _ => wholePiece_le _ _ _)
  have rank := (component_totals_on_labels F.G K.barrier e Finset.univ 7).1
  change matchingEdges P=∑i:↥K.positive,K.pieceCapacity i at rank
  have lower := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥K.positive)) (fun q _ => small q)
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id,←rank] at lower
  change K.positive.ncard*K.pieceCapacity p≤matchingEdges P at lower
  rw [(strict_seven_four_positive_pieces F paid seven K).1] at lower
  exact lower.trans (rank_le_of_copy (SimpleGraph.Copy.ofLE P F.G sub))

theorem height_below_empty_column {s t r h:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ)
    (live:0<rowCount s t r) (empty:widthAt n m r h=0) : diagonal n m (r+2)<h := by
  by_contra! tall
  have mem : 0∈offsetsAt n m r h := by simp [offsetsAt,live,tall]
  exact (Finset.notMem_empty 0) ((Finset.card_eq_zero.mp empty) ▸ mem)

#print axioms four_minimum_blocks_fit_matching
#print axioms height_below_empty_column
end JSP452Audit.StarHost
