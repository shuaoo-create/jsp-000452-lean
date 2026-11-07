import StrictPaidPieceMenus
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_seven_four_positive_pieces (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) (K:DegreeRegion F.G 7) :
    K.positive.ncard=4 ∧ 11≤edgeSurplus (F.G.induce K.positiveCore) 7 ∧
    edgeSurplus (F.G.induce K.positiveCore) 7≤12 ∧
    ∀c:↥K.positive,2≤K.pieceWeight c ∧ K.pieceWeight c≤3 ∧ 4≤K.pieceCapacity c := by
  classical
  let _ := Fintype.ofFinite ↥K.positive
  obtain ⟨_,_,_,degree,_,_⟩ := minimal_rank_exact_source F paid
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤7 := (degree x).trans_eq seven
  have exp := (strict_seven_original_peak F paid seven).2.1
  have lower := K.weight_identity cap
  rw [exp] at lower
  have dom := positivePieces_dominate F.G K.barrier K.pieces 7
  change edgeSurplus (F.G.induce K.core) 7≤edgeSurplus (F.G.induce K.positiveCore) 7 at dom
  have lo : 11≤edgeSurplus (F.G.induce K.positiveCore) 7 := by omega
  have upper (c:↥K.positive) : K.pieceWeight c≤3 := (K.positive_piece_bounds cap c).2.1
  have bound := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥K.positive)) (fun c _ => upper c)
  rw [←K.piece_weight_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card] at bound
  have max := seven_positive_piece_upper F paid seven K
  change K.positive.ncard≤4 at max
  change edgeSurplus (F.G.induce K.positiveCore) 7≤(K.positive.ncard:ℤ)*3 at bound
  have count : K.positive.ncard=4 := by omega
  refine ⟨count,lo,by omega,?_⟩
  intro c
  have other := Finset.sum_le_sum (s:=Finset.univ.erase c) (fun i _ => upper i)
  rw [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ c),Finset.card_univ,
    ←Nat.card_eq_fintype_card,nsmul_eq_mul] at other
  change (∑i∈Finset.univ.erase c,K.pieceWeight i)≤((K.positive.ncard-1:ℕ):ℤ)*3 at other
  have total := Finset.add_sum_erase (s:=Finset.univ) K.pieceWeight (Finset.mem_univ c)
  rw [←K.piece_weight_sum] at total
  have each : 2≤K.pieceWeight c := by rw [count] at other;omega
  let Q := c.val.toSimpleGraph
  let _ : Nonempty c.val.supp := c.val.nonempty_supp.to_subtype
  have capQ (x:c.val.supp) : Nat.card (Q.neighborSet x)≤7 :=
    (induced_neighbor_count_le (F.G.induce K.barrierᶜ) c.val.supp x).trans
      ((induced_neighbor_count_le F.G K.barrierᶜ x.val).trans (cap x.val.val))
  have big := (positive_core_caps Q (K.critical c.val).2 7 capQ c.property.2).1
  have order := factorCritical_order_rank Q (K.critical c.val).2 c.val.nonempty_supp.to_subtype.some
  change Nat.card c.val.supp=2*K.pieceCapacity c+1 at order
  change 7+1≤Nat.card c.val.supp at big
  exact ⟨each,upper c,by omega⟩

#print axioms strict_seven_four_positive_pieces
end JSP452Audit.StarHost
