import SumTheEntireOriginalHighPlatformProfileIncludingItsUnitColumn
namespace JSP452Audit.StarHost
open SimpleGraph

theorem partial_profile_area_le {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (r B:ℕ) :
    (∑j∈Finset.range B,widthAt n m r (j+1))≤rowEnergy n m r := by
  let h := max B (diagonal n m (r+2))
  have all := profile_area_after_any_shift hs ht n m hn hm (show r≤r from le_rfl) (show diagonal n m (r+2)≤h from Nat.le_max_right _ _)
  rw [all]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_max_left _ _)) (fun _ _ _ => Nat.zero_le _)

theorem total_fixed_platform_price {A:Type*} [Finite A] (C:SimpleGraph A) {s t r b D H:ℕ}
    (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (later:r≤b) (top:diagonal n m (r+2)≤D+1) (red:n ⟨0,hs⟩≤H) (blue:m ⟨0,ht⟩≤H)
    (head:10≤H) (ratio:9*Nat.card A≤19*matchingEdges C) (positive:0<Nat.card A/7) :
    let l := Nat.card A/7
    let K := fixedCoreList C n l
    let V := fixedCoreList C m l
    rowEnergy n m b≤rowEnergy K V (b+l)+∑j∈Finset.range (D+1),protectedColumnFee (matchingEdges C) (Nat.card A) H j := by
  intro l K V
  have area := profile_area_after_any_shift hs ht n m hn hm later top
  have each (j:ℕ) : widthAt n m b (j+1)≤widthAt K V (b+l) (j+1)+protectedColumnFee (matchingEdges C) (Nat.card A) H j := by
    by_cases live:0<widthAt n m b (j+1)
    · obtain ⟨x,y,w⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega : 0<j+1) live
      have win : WinsHeight n m b (j+1) x y := w
      have xh := ((original_threshold_prefix n hn x ⟨0,hs⟩).2 win.2.2.2.1).trans red
      have yh := ((original_threshold_prefix m hm y ⟨0,ht⟩).2 win.2.2.2.2.1).trans blue
      have ht := win.2.2.1
      have fee := protected_pair_fee (matchingEdges C) (Nat.card A) H j x y ratio head win.1 win.2.1 xh yh (by omega)
      have pay := fixed_lists_price_original_winner C n m hn hm l positive win
      change _≤widthAt K V (b+l) (j+1)+_ at pay
      exact pay.trans (Nat.add_le_add_left fee _)
    · omega
  have sum := Finset.sum_le_sum (s:=Finset.range (D+1)) (fun j _ => each j)
  rw [Finset.sum_add_distrib,←area] at sum
  have kn := protected_demand_antitone n _ hn ((componentBudget C n).entries_antitone n hn) l
  have vm := protected_demand_antitone m _ hm ((componentBudget C m).entries_antitone m hm) l
  have p : 0<l := positive
  have keep := partial_profile_area_le (show 0<min s ((componentBudget C n).len+l) by omega)
    (show 0<min t ((componentBudget C m).len+l) by omega) K V kn vm (b+l) (D+1)
  omega

#print axioms partial_profile_area_le
#print axioms total_fixed_platform_price
end JSP452Audit.StarHost
