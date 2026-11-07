import EvenCapOmittedWeight
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_even_positive_weight_ceiling (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (p:ℕ) (half:2≤p) (even:diagonal F.n F.m (F.r+2)-1=2*p) (K:DegreeRegion F.G (2*p)) :
    edgeSurplus (F.G.induce K.positiveCore) (2*p)≤(highestWidth F.n F.m F.r:ℤ)-1+
      (p:ℤ)*((p:ℤ)-1)+((oddRegularComponents F.G (2*p)).ncard:ℤ) := by
  classical
  let _ := Fintype.ofFinite ↥K.positive
  obtain ⟨_,_,_,degree,_,_⟩ := minimal_rank_exact_source F paid
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤2*p := (degree x).trans_eq even
  have top : diagonal F.n F.m (F.r+2)=2*p+1 := by omega
  have hpos := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row degree).1
  have each (q:↥K.positive) : K.pieceWeight q≤(p:ℤ) := by
    have bound := (K.positive_piece_bounds cap q).2.1
    rwa [show 2*p/2=p by omega] at bound
  have capped := even_full_weight_count p K
  have total := K.piece_weight_sum
  by_cases small:Fintype.card ↥K.positive≤p
  · have loss := omitted_even_weight_bound K.pieceWeight p (by omega) each Finset.univ (by simpa using small)
    rw [←total] at loss
    omega
  obtain ⟨T,many,ord,c,mem,largest⟩ := omit_half_cap_largest K.pieceCapacity p half (by omega)
  let Z := K.pieceCapacity c
  let b := Z-(F.r+1)
  obtain ⟨U,size,ind,full,away⟩ := half_cap_spare_vertices p (by omega) K T Z b many
    (fun q hq => ord q hq c mem) cap (Nat.sub_le _ _)
  have fit (q) (hq:q∈T) : K.pieceCapacity q≤F.r+U.ncard+1 := by
    have le := largest q hq
    change K.pieceCapacity q≤Z at le
    rw [size];dsimp [b];omega
  have positive := (K.positive_piece_bounds cap c).2.2.2
  have some := Finset.single_le_sum (f:=K.pieceCapacity) (fun _ _ => Nat.zero_le _) mem
  have weight := strict_piece_menu_weight F paid (2*p) top K T U ind full away fit (by omega)
  have removed := omitted_even_weight_bound K.pieceWeight p (by omega) each Tᶜ many.le
  have partition := Finset.sum_add_sum_compl T K.pieceWeight
  rw [←total] at partition
  omega

theorem strict_even_exposure_inventory (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (p:ℕ) (half:2≤p) (even:diagonal F.n F.m (F.r+2)-1=2*p) :
    (p:ℤ)*(minimumExposure F.G (2*p):ℤ)≤(highestWidth F.n F.m F.r:ℤ)-1+
      (p:ℤ)*((p:ℤ)-1)+((oddRegularComponents F.G (2*p)).ncard:ℤ) := by
  obtain ⟨K⟩ := degreeRegion_exists F.G (2*p)
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤2*p :=
    ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq even
  have lower := K.weight_identity cap
  have dom := positivePieces_dominate F.G K.barrier K.pieces (2*p)
  change edgeSurplus (F.G.induce K.core) (2*p)≤edgeSurplus (F.G.induce K.positiveCore) (2*p) at dom
  have upper := strict_even_positive_weight_ceiling F paid p half even K
  push_cast at lower
  rw [mul_assoc (2:ℤ)] at lower
  omega

#print axioms strict_even_positive_weight_ceiling
#print axioms strict_even_exposure_inventory
end JSP452Audit.StarHost
