import ExcludeEveryActualThreeHeadWinnerAtTheOnlyRemainingGap
namespace JSP452Audit.StarHost
open SimpleGraph

theorem gap_one_fixed_area_with_real_top_tax {A:Type*} [Finite A] (C:SimpleGraph A) {s t b H l fee:ℕ}
    (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (red:n ⟨0,hs⟩≤H) (blue:m ⟨0,ht⟩≤H)
    (head:9≤H) (ratio:16*Nat.card A≤35*matchingEdges C) (positive:0<l)
    (lo:Nat.card A/6≤l) (hi:l≤Nat.card A/3) :
    let K := fixedCoreList C n l
    let V := fixedCoreList C m l
    widthAt n m b (H+1)≤widthAt K V (b+l) (H+1)+fee →
    (∑j∈Finset.range (H+1),widthAt n m b (j+1))+Nat.card A/3≤rowEnergy K V (b+l)+(∑j∈Finset.range (H+1),lastGapFixedFee (matchingEdges C) (Nat.card A) H l j)+fee := by
  intro K V top
  have each (j:ℕ) (last:j≤H) : widthAt n m b (j+1)≤widthAt K V (b+l) (j+1)+lastGapFixedFee (matchingEdges C) (Nat.card A) H l j := by
    by_cases live:0<widthAt n m b (j+1)
    · obtain ⟨x,y,w⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega : 0<j+1) live
      have win : WinsHeight n m b (j+1) x y := w
      have xh := ((original_threshold_prefix n hn x ⟨0,hs⟩).2 win.2.2.2.1).trans red
      have yh := ((original_threshold_prefix m hm y ⟨0,ht⟩).2 win.2.2.2.2.1).trans blue
      have ht := win.2.2.1
      have fee := last_gap_pair_price (matchingEdges C) (Nat.card A) H l j x y ratio head lo hi win.1 win.2.1 xh yh (by omega) last
      have pay := fixed_lists_price_original_winner C n m hn hm l positive win
      change _≤widthAt K V (b+l) (j+1)+_ at pay
      exact pay.trans (Nat.add_le_add_left fee _)
    · omega
  have sum := Finset.sum_le_sum (s:=Finset.range H) (fun j hj => each j (by have := Finset.mem_range.mp hj;omega))
  rw [Finset.sum_add_distrib] at sum
  have kn := protected_demand_antitone n _ hn ((componentBudget C n).entries_antitone n hn) l
  have vm := protected_demand_antitone m _ hm ((componentBudget C m).entries_antitone m hm) l
  have p : 0<l := positive
  have keep := partial_profile_area_le (show 0<min s ((componentBudget C n).len+l) by omega)
    (show 0<min t ((componentBudget C m).len+l) by omega) K V kn vm (b+l) (H+1)
  rw [Finset.sum_range_succ] at keep
  rw [Finset.sum_range_succ,Finset.sum_range_succ]
  rw [show lastGapFixedFee (matchingEdges C) (Nat.card A) H l H=Nat.card A/3 by simp [lastGapFixedFee]]
  omega

#print axioms gap_one_fixed_area_with_real_top_tax
end JSP452Audit.StarHost
