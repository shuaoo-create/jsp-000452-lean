import TrimUniformStarsAtOriginalPorts
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem seven_block_touched_bound (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) (K:DegreeRegion F.G 7) (p:↥K.positive)
    (R:SimpleGraph F.X) (sub:R≤SevenPiece.erased F K p) (a u:ℕ) (two:2≤a)
    (f:(forest (fun _:Fin u => a)).Copy (R⊔wholePiece F.G K.barrier p.val)) :
    (touchedStars R (wholePiece F.G K.barrier p.val) (fun _:Fin u => a) f).ncard≤(2*K.pieceCapacity p+4)/3 := by
  let U := cutPieceSet F.G K.barrier p.val
  let P := wholePiece F.G K.barrier p.val
  have count := three_vertices_per_touched_star F.G R P U (sub.trans sdiff_le) (wholePiece_le _ _ _) (fun _ _ e => e.2.1) a two f
  have ports := strict_seven_piece_has_one_or_three_ports F paid seven K p
  have bound : crossCount F.G U Uᶜ≤3 := by
    rcases ports with ⟨_,one⟩|⟨_,three⟩
    · change crossCount F.G U Uᶜ=1 at one;omega
    · change crossCount F.G U Uᶜ=3 at three;omega
  have order := factorCritical_order_rank p.val.toSimpleGraph (K.critical p.val).2 p.val.nonempty_supp.to_subtype.some
  have size : U.ncard=2*K.pieceCapacity p+1 := (Nat.card_congr (cutPieceVertexEquiv F.G K.barrier p.val)).symm.trans order
  rw [size] at count
  change 3*(touchedStars R P (fun _:Fin u => a) f).ncard≤_ at count
  change (touchedStars R P (fun _:Fin u => a) f).ncard≤_
  omega

theorem seven_block_restored_typed_width (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) (K:DegreeRegion F.G 7) (p:↥K.positive)
    (a b L:ℕ) (ra:2≤a) (bb:2≤b) (typed:ExactTypedWidth F.G a b L)
    (wide:2*((2*K.pieceCapacity p+4)/3)<L) :
    ExactTypedWidth (SevenPiece.erased F K p) a b (L-(2*K.pieceCapacity p+4)/3) := by
  let M := (2*K.pieceCapacity p+4)/3
  change 2*M<L at wide
  change ExactTypedWidth (SevenPiece.erased F K p) a b (L-M)
  rcases typed with zero|⟨u,v,hu,hv,width,force⟩
  · omega
  · by_cases red:M<u
    · have next := uniform_after_restoring_red F.G (wholePiece F.G K.barrier p.val) (wholePiece_le _ _ _) a b u v M
        (fun R sub f => seven_block_touched_bound F paid seven K p R sub a u ra f) force
      exact Or.inr ⟨u-M,v,by omega,hv,by omega,next⟩
    · have blue:M<v := by omega
      have next := uniform_after_restoring_red F.G (wholePiece F.G K.barrier p.val) (wholePiece_le _ _ _) b a v u M
        (fun R sub f => seven_block_touched_bound F paid seven K p R sub b v bb f) (forces_swap force)
      exact Or.inr ⟨u,v-M,hu,by omega,by omega,forces_swap next⟩

#print axioms seven_block_touched_bound
#print axioms seven_block_restored_typed_width
end JSP452Audit.StarHost
