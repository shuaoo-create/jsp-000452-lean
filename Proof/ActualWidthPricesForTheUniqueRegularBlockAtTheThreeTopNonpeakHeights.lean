import TheTwoLowerWinningColumnsOnTheSameRegularExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem regular_third_gap_block_widths (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (p:ℕ)
    (B:RegularOddBlock F.G p) (degree:diagonal F.n F.m (F.r+2)-1=2*p)
    (head:max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)+3=2*p) (one:highestWidth F.n F.m F.r=1) :
    let N := Nat.card B.piece.supp
    let W := widthAt F.n F.m F.r
    let O := B.outside
    (∀j,0<j → W j≤uniformEnvelope O j+B.P) ∧
    (∀x y,WinsHeight F.n F.m F.r (2*p) x y →
      4≤min x y ∧ ExactTypedWidth O x y (W (2*p)-N/5)) ∧
    (∀x y,WinsHeight F.n F.m F.r (2*p-1) x y → 3≤min x y ∧
      (ExactTypedWidth O x y (W (2*p-1)-N/4) ∨ W (2*p-1)≤N/4+N/7) ∧
      W (2*p-1)≤uniformEnvelope O (2*p-1)+N/3) ∧
    (∀x y,WinsHeight F.n F.m F.r (2*p-2) x y → 2≤min x y ∧
      (ExactTypedWidth O x y (W (2*p-2)-N/3) ∨ W (2*p-2)≤B.P)) := by
  intro N W O
  let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
  have deg := strict_source_degree_at_least_eleven F paid
  rw [degree] at deg
  change H+3=2*p at head
  have total := (strict_double_head_gap_range F paid).2.1
  rw [degree] at total
  have peak := width_at_peak F.hs F.ht F.n F.m F.hn F.hm F.r
  rw [show diagonal F.n F.m (F.r+2)=2*p+1 by omega,one] at peak
  have reg (v:B.piece.supp) : Nat.card (B.inside.neighborSet v)=2*p := (component_degree_eq F.G B.piece v).trans (B.full.2 _ v.property)
  have limit := (strict_closed_union_lengths F paid B.piece.supp
    (fun _ hx _ e => (B.piece.mem_supp_congr_adj e).mp hx) (fun x hx => (B.full.2 x hx).trans degree.symm)).1
  have short : matchingEdges B.inside<min F.s F.t := by change matchingEdges B.inside+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t at limit;omega
  obtain ⟨floor,order,rk,_,_⟩ := B.original_geometry
  change N=2*B.P+1 at order
  have row := B.original_row _ _ F.row
  have heads (j x y:ℕ) (win:WinsHeight F.n F.m F.r j x y) : x≤H ∧ y≤H := by
    exact ⟨((original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 win.2.2.2.1).trans (Nat.le_max_left _ _),
      ((original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 win.2.2.2.2.1).trans (Nat.le_max_right _ _)⟩
  have fallback (j x y:ℕ) (win:WinsHeight F.n F.m F.r j x y) := monochrome_or_two_bounded_counts O B.inside F.n F.m F.hn F.hm row win
  constructor
  · intro j pos
    by_cases live:0<W j
    · obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm pos live
      have win : WinsHeight F.n F.m F.r j x y := w
      have estimate := physical_rectangle_tax O B.inside F.n F.m F.hn F.hm F.pn F.pm win.1 win.2.1
        win.2.2.2.1 win.2.2.2.2.1 rk (by change N≤_;omega) short row
      rw [←win.2.2.2.2.2,win.2.2.1] at estimate;exact estimate
    · omega
  constructor
  · intro x y win
    obtain ⟨ax,bx⟩ := heads _ x y win
    have sum := win.2.2.1
    have minH : 4≤min x y := by omega
    have actual := even_total_top_typed O B.inside F.n F.m F.hs F.ht F.hn F.hm row win (fun v => (reg v).le) total peak.le
    refine ⟨minH,actual_typed_width_down O actual ?_⟩
    have lower : N/(min x y+1)≤N/5 := Nat.div_le_div_left (by omega) (by decide)
    change W (2*p)-N/5≤W (2*p)-N/(min x y+1);omega
  constructor
  · intro x y win
    obtain ⟨ax,bx⟩ := heads _ x y win
    have sum := win.2.2.1
    have minH : 3≤min x y := by omega
    have shape := fallback _ x y win
    have a : N/(x+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
    have b : N/(y+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
    refine ⟨minH,?_,?_⟩
    · rcases shape with actual|dead
      · left;apply actual_typed_width_down O actual
        have lower : N/(min x y+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
        change W _-N/4≤W _-N/(min x y+1);omega
      · right;change W _≤N/(x+1)+N/(y+1) at dead
        rcases (show 6≤x ∨ 6≤y by omega) with left|right
        · have bound : N/(x+1)≤N/7 := Nat.div_le_div_left (by omega) (by decide : 0<7);omega
        · have bound : N/(y+1)≤N/7 := Nat.div_le_div_left (by omega) (by decide : 0<7);omega
    · have tax := sharp_summand_coordinate O B.inside F.n F.m F.hn F.hm win.1 win.2.1 win.2.2.2.1 win.2.2.2.2.1 row
      let J := actualCoordinateLoss (matchingEdges B.inside) N F.r x y
      have no : ¬(x=1 ∨ y=1) := by omega
      change ExactTypedWidth O x y (originalThresholdCount F.n x+originalThresholdCount F.m y-1-F.r-pointCoordinateTax (matchingEdges B.inside) N F.r x y) at tax
      have same : J=pointCoordinateTax (matchingEdges B.inside) N F.r x y := if_neg no
      rw [←win.2.2.2.2.2,←same] at tax
      change ExactTypedWidth O x y (W (2*p-1)-J) at tax
      have q : 3*J≤N := by
        by_cases r3:x=3
        · have t := bounded_point_tax_ratio (matchingEdges B.inside) N F.r x y 3 7 (by decide) (by decide) (by omega) (by omega)
          change 31*J≤10*N at t;omega
        by_cases b3:y=3
        · have t := bounded_point_tax_ratio (matchingEdges B.inside) N F.r x y 7 3 (by decide) (by decide) (by omega) (by omega)
          change 31*J≤10*N at t;omega
        have t := bounded_point_tax_ratio (matchingEdges B.inside) N F.r x y 4 4 (by decide) (by decide) (by omega) (by omega)
        change 24*J≤8*N at t;omega
      rcases tax with zero|⟨u,v,hu,hv,len,force⟩
      · omega
      · have env := uniform_pair_le_envelope O x y u v (2*p-1) win.1 win.2.1 hu hv win.2.2.1 force
        rw [len] at env;omega
  · intro x y win
    obtain ⟨ax,bx⟩ := heads _ x y win
    have sum := win.2.2.1
    have minH : 2≤min x y := by omega
    refine ⟨minH,?_⟩
    rcases fallback _ x y win with actual|dead
    · left;apply actual_typed_width_down O actual
      have lower : N/(min x y+1)≤N/3 := Nat.div_le_div_left (by omega) (by decide)
      change W _-N/3≤W _-N/(min x y+1);omega
    · right;change W _≤N/(x+1)+N/(y+1) at dead
      have a : N/(x+1)≤N/3 := Nat.div_le_div_left (by omega) (by decide)
      have b : N/(y+1)≤N/3 := Nat.div_le_div_left (by omega) (by decide)
      rcases (show 5≤x ∨ 5≤y by omega) with red|blue
      · have bound : N/(x+1)≤N/6 := Nat.div_le_div_left (by omega) (by decide : 0<6);omega
      · have bound : N/(y+1)≤N/6 := Nat.div_le_div_left (by omega) (by decide : 0<6);omega

#print axioms regular_third_gap_block_widths
end JSP452Audit.StarHost
