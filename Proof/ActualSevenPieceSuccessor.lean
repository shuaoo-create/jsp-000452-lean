import FourPieceRankBeforeDescent
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

namespace SevenPiece
variable (F:StrictFamily.{u}) (K:DegreeRegion F.G 7) (p:↥K.positive)
abbrev erased := F.G \ wholePiece F.G K.barrier p.val
noncomputable abbrev cost := K.pieceCapacity p-(F.r+1)
noncomputable abbrev nextRow := F.r+(K.pieceCapacity p+cost F K p)

structure Descent where
  stage : Set F.X
  removed : Set F.X
  complete : CompleteDegreeStage (erased F K p) 7 stage
  room : 6*K.pieceCapacity p+3≤7*stage.ncard
  short : stage.ncard<cost F K p
  contains_stage : stage⊆removed
  count : removed.ncard=cost F K p
  cap : ∀x,Nat.card (((erased F K p).induce removedᶜ).neighborSet x)≤6
  row : ForcingRow ((erased F K p).induce removedᶜ) F.s F.t (padDemand F.n) (padDemand F.m) (nextRow F K p)
  live : 0<rowCount F.s F.t (nextRow F K p)
  smaller : rowCount F.s F.t (nextRow F K p)<F.rank
  height : diagonal F.n F.m (nextRow F K p+2)≤7
  upper : (((erased F K p).induce removedᶜ).edgeSet.ncard:ℤ)-(rowEnergy F.n F.m (nextRow F K p):ℤ)≤
    (widthAt F.n F.m F.r 7:ℤ)-(K.pieceCapacity p:ℤ)-(stage.ncard:ℤ)-K.pieceWeight p

theorem actual_descent (paid:AllSmallerPaid.{u} F.rank) (seven:diagonal F.n F.m (F.r+2)-1=7)
    (minimum:∀q:↥K.positive,K.pieceCapacity p≤K.pieceCapacity q) : Nonempty (Descent F K p) := by
  obtain ⟨_,_,rank,degree,_,_⟩ := minimal_rank_exact_source F paid
  let H := erased F K p
  let z := K.pieceCapacity p
  let t := cost F K p
  let k := z+t
  have capH (x) : Nat.card (H.neighborSet x)≤7 :=
    (Set.ncard_le_ncard (show H.neighborSet x⊆F.G.neighborSet x from fun _ h => h.1)).trans ((degree x).trans_eq seven)
  obtain ⟨E,B,many,full,stage,room⟩ := strict_seven_seeded_stage F paid seven K p minimum
  have short := strict_seven_stage_short F paid seven K p B stage
  obtain ⟨A,sub,size,edges,cap⟩ := seven_six_prefix_exists H z t E B capH many full stage short (Nat.sub_le _ _)
  have price := single_piece_actual_cost K p
  change (F.G.edgeSet.ncard:ℤ)=(H.edgeSet.ncard:ℤ)+7*(z:ℤ)+K.pieceWeight p at price
  have next := single_piece_actual_row K p A _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) (by rw [size];dsimp [t,cost];omega) F.row
  have index : F.r+A.ncard+K.pieceCapacity p=nextRow F K p := by rw [size];dsimp [nextRow,t];omega
  rw [index] at next
  have reach := four_minimum_blocks_fit_matching F paid seven K p minimum
  change 4*z≤matchingEdges F.G at reach
  have zpos := seven_minimum_capacity_at_least_seventeen F paid seven K p minimum
  change 17≤z at zpos
  have amt : k<F.rank := by dsimp [k,t,cost,z] at *;omega
  have pos : 0<k := by dsimp [k];omega
  have nextSize : rowCount F.s F.t (nextRow F K p)=F.rank-k := by
    change F.s+F.t-1-(F.r+k)=(F.s+F.t-1-F.r)-k;omega
  have live : 0<rowCount F.s F.t (nextRow F K p) := by rw [nextSize];omega
  have smaller : rowCount F.s F.t (nextRow F K p)<F.rank := by rw [nextSize];omega
  have top : diagonal F.n F.m (F.r+2)=8 := by omega
  have peak := (strict_seven_original_peak F paid seven).1
  have original : widthAt F.n F.m F.r 8=1 := by rw [←top,width_at_peak F.hs F.ht F.n F.m F.hn F.hm,peak]
  have empty := widthAt_shift F.hs F.ht F.n F.m F.hn F.hm F.r k 8
  rw [original] at empty
  have height := height_below_empty_column F.n F.m live (show widthAt F.n F.m (nextRow F K p) 8=0 from by change widthAt F.n F.m (F.r+k) 8=0;omega)
  have tax := prefix_at_two_top_columns F.hs F.ht F.n F.m F.hn F.hm 6 top k
  rw [peak] at tax
  have strict := F.strict
  refine ⟨⟨B,A,stage,room,short,sub,size,cap,next,live,smaller,by omega,?_⟩⟩
  change ((H.induce Aᶜ).edgeSet.ncard:ℤ)-(rowEnergy F.n F.m (F.r+k):ℤ)≤(widthAt F.n F.m F.r 7:ℤ)-(z:ℤ)-(B.ncard:ℤ)-K.pieceWeight p
  change H.edgeSet.ncard=(H.induce Aᶜ).edgeSet.ncard+6*t+B.ncard at edges
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k)+6*k+widthAt F.n F.m F.r 7+1 at tax
  have expand : k=z+t := rfl
  omega

#print axioms actual_descent
end SevenPiece
end JSP452Audit.StarHost
