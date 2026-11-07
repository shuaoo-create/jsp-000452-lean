import RealPointCoverColumnTax
namespace JSP452Audit.StarHost
open SimpleGraph

theorem small_tax_trichotomy (f g x y N K r:ℕ) (red:2≤x) (blue:2≤y) (order:N≤2*K+2) :
    f+g-1-r≤K ∨ N-x*f≤K ∨ N-y*g≤K := by
  have a := Nat.mul_le_mul_right f red
  have b := Nat.mul_le_mul_right g blue
  omega

theorem physical_rectangle_tax {X Y:Type*} [Finite X] [Finite Y]
    (O:SimpleGraph X) (C:SimpleGraph Y) {s t r x y K:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀i,1≤m i) (rx:0<x) (byh:0<y)
    (red:0<originalThresholdCount n x) (blue:0<originalThresholdCount m y)
    (rank:matchingEdges C≤K) (order:Nat.card Y≤2*K+2) (length:matchingEdges C<min s t)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    originalThresholdCount n x+originalThresholdCount m y-1-r≤uniformEnvelope O (x+y-1)+K := by
  let f := originalThresholdCount n x
  let g := originalThresholdCount m y
  let P := matchingEdges C
  let N := Nat.card Y
  let a := min P (N/(x+1))
  let b := min P (N/(y+1))
  have pack (w:ℕ) (pos:0<w) : UniformPackCap C w (min P (N/(w+1))) := by
    intro l copy
    have size := uniform_pack_order_cap C w pos Set.univ (fun _ _ _ => Set.mem_univ _) l copy
    rw [Set.ncard_univ] at size
    exact le_min ((uniform_pack_rank_cap C w pos) l copy) size
  by_cases liveR : a<f
  · exact (mono_red_rectangle O C n m hn hm rx byh (pack x rx) liveR blue row).trans
      (Nat.add_le_add_left ((min_le_left _ _).trans rank) _)
  by_cases liveB : b<g
  · exact (mono_blue_rectangle O C n m hn hm rx byh red (pack y byh) liveB row).trans
      (Nat.add_le_add_left ((min_le_left _ _).trans rank) _)
  have ns := length.trans_le (Nat.min_le_left _ _)
  have mt := length.trans_le (Nat.min_le_right _ _)
  have highR : 2≤x := by
    by_contra! small
    have eq : x=1 := by omega
    have ff : f=s := by dsimp only [f];rw [eq,original_threshold_one n pn]
    have lim : a≤matchingEdges C := min_le_left _ _
    omega
  have highB : 2≤y := by
    by_contra! small
    have eq : y=1 := by omega
    have gg : g=t := by dsimp only [g];rw [eq,original_threshold_one m pm]
    have lim : b≤matchingEdges C := min_le_left _ _
    omega
  have fx : f≤N/(x+1) := (Nat.le_of_not_gt liveR).trans (min_le_right _ _)
  have gy : g≤N/(y+1) := (Nat.le_of_not_gt liveB).trans (min_le_right _ _)
  have rfit : (x+1)*f≤N := Nat.mul_comm f (x+1) ▸ ((Nat.le_div_iff_mul_le (by omega)).mp fx)
  have bfit : (y+1)*g≤N := Nat.mul_comm g (y+1) ▸ ((Nat.le_div_iff_mul_le (by omega)).mp gy)
  rcases small_tax_trichotomy f g x y N K r highR highB order with base|aCap|bCap
  · change f+g-1-r≤_;omega
  · exact (point_cover_red_tax O C n m hn hm rx byh red blue rfit row).trans (Nat.add_le_add_left aCap _)
  · exact (point_cover_blue_tax O C n m hn hm rx byh red blue bfit row).trans (Nat.add_le_add_left bCap _)

theorem closed_union_column_tax {X:Type*} [Finite X] (G:SimpleGraph X) (U:Set X)
    (closed:∀v∈U,∀w,G.Adj v w → w∈U) {s t r j K:ℕ} (hs:0<s) (ht:0<t)
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀i,1≤m i)
    (height:0<j) (rank:matchingEdges (G.induce U)≤K) (order:U.ncard≤2*K+2)
    (length:matchingEdges (G.induce U)<min s t) (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    widthAt n m r j≤uniformEnvelope (G.induce Uᶜ) j+K := by
  by_cases active : 0<widthAt n m r j
  · obtain ⟨x,y,rx,byh,eq,rf,bg,win⟩ := original_column_real_winner hs ht n m hn hm pn pm height active
    have price := physical_rectangle_tax (G.induce Uᶜ) (G.induce U) n m hn hm pn pm rx byh rf bg
      rank order length (closed_union_sum_row G U closed row)
    rwa [←win,eq] at price
  · omega

#print axioms small_tax_trichotomy
#print axioms physical_rectangle_tax
#print axioms closed_union_column_tax
end JSP452Audit.StarHost
