import NonunitExteriorActualLayers
namespace JSP452Audit.StarHost
open SimpleGraph

theorem one_exterior_offset_cut {s t r D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (ht : 0<t) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (room : t+∑j,(m j-1)/2≤matchingEdges (G.induce K.core)) (j : ℕ) (pos : 0<j) :
    let f := originalThresholdCount n j
    2*(f+t-1-r)≤2*(K.roots.ncard+matchingEdges (G.induce K.core)+uniformEnvelope (G.induce K.rest) j)+f := by
  intro f
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let Y := ∑j,(m j-1)/2
  let w := μ+1-(t+Y)
  let V := halfOrderBudget m (μ-w)
  obtain ⟨v,actual⟩ := exact_axis_repair_inventory G K n m hn hm pn pm ht row room
  change 0<V.len at v
  have rep := actual j pos
  change 2*w<f → f-2*w+V.len-1-(r+a)≤uniformEnvelope (G.induce K.rest) j ∧ _ at rep
  change t+Y≤μ at room
  have key : w+t+Y=μ+1 := by dsimp [w];omega
  change 2*(f+t-1-r)≤2*(a+μ+uniformEnvelope (G.induce K.rest) j)+f
  by_cases many : 2*w<f
  · have pay := (rep many).1;omega
  · omega

theorem quintic_red_prefix_at_peak {s t r x b : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (head : n ⟨0,hs⟩=5) (blue : m ⟨0,ht⟩=b)
    (top : diagonal n m (r+2)=6) (level : x+b=7) (large : 2≤b) :
    originalThresholdCount n x≤r+highestWidth n m r := by
  have px := (original_threshold_prefix n hn x ⟨0,hs⟩).1 (show x≤n ⟨0,hs⟩ by omega)
  have py := (original_threshold_prefix m hm b ⟨0,ht⟩).1 blue.ge
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=x) (b:=b) (h:=6) (by omega) px py
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  rcases Nat.eq_zero_or_pos (highestWidth n m r) with z|z <;> omega

theorem quintic_ternary_last_axis {s t r : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (head : n ⟨0,hs⟩=5) (blue : m ⟨0,ht⟩=3) (top : diagonal n m (r+2)=6)
    (live : 0<rowCount s t r) (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t) :
    widthAt n m r 5≤t-1 := by
  have win := full_opposite_three_options hs ht n m hn hm pn pm (show 3≤5 by decide)
    (actual_height_positive n m live top 5 (by decide)) budget
  have p := (original_threshold_prefix n hn 5 ⟨0,hs⟩).1 head.ge
  have b := (original_threshold_prefix m hm 3 ⟨0,ht⟩).1 blue.ge
  have anti := above_top_prefix_sum hs ht n m hn hm (D:=5) top (by decide : 5+1<5+3-1) p b
  rcases win with ax|⟨hi,_⟩|⟨hi,_⟩
  · omega
  · have bad := (original_threshold_prefix m hm 5 ⟨0,ht⟩).2 hi;omega
  · have bad := (original_threshold_prefix m hm (5-1) ⟨0,ht⟩).2 hi;omega

#print axioms one_exterior_offset_cut
#print axioms quintic_red_prefix_at_peak
#print axioms quintic_ternary_last_axis
end JSP452Audit.StarHost