import TenDegreeNonunitColumnsCostAtMostTheHalfOrder
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_port_every_lower_column {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ}
    (W:TenPortSupport G K h) (positive:1≤h) {s t r:ℕ} (hs:0<s) (ht:0<t)
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀i,1≤m i)
    (ls:W.rank<s) (lt:W.rank<t) (row:ForcingRow G s t (padDemand n) (padDemand m) r) (j:ℕ) (live:0<j) :
    widthAt n m r j≤uniformEnvelope W.outside j+W.half := by
  by_cases present:0<widthAt n m r j
  · obtain ⟨a,b,pa,pb,height,red,blue,width⟩ := original_column_real_winner hs ht n m hn hm pn pm live present
    have fit : W.rank≤W.half := (W.size_and_fee positive).2.2.2.2.1
    have unitTax : W.starTax 1≤W.rank := Nat.min_le_left _ _
    by_cases one:a=1
    · subst a
      have many : W.starTax 1<originalThresholdCount n 1 := by rw [original_threshold_one n pn];omega
      have pay := W.typed_width_envelope pa pb height (W.active_port_rectangle n m hn hm many blue row)
      rw [W.exterior_inventory] at pay;omega
    by_cases two:b=1
    · subst b
      have many : W.starTax 1<originalThresholdCount m 1 := by rw [original_threshold_one m pm];omega
      have pay := W.typed_width_envelope pb pa (show 1+a-1=j by omega)
        (W.active_port_rectangle m n hm hn many red (swap_positive_forcing_row _ _ _ row))
      rw [W.exterior_inventory] at pay;omega
    rw [←W.exterior_inventory]
    exact ten_nonunit_port_column W positive n m hn hm (by omega) (by omega) ⟨pa,pb,height,red,blue,width⟩ row
  · omega

#print axioms ten_port_every_lower_column
end JSP452Audit.StarHost
