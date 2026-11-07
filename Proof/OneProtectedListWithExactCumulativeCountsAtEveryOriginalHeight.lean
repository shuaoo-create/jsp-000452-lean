import TheSurvivingLargeGapPlatformPaysTheRequiredHighDegreePrefix
namespace JSP452Audit.StarHost

def protectedDemand {s t:ℕ} (n:Fin s→ℕ) (R:Fin t→ℕ) (l:ℕ) (i:Fin (min s (t+l))) : ℕ :=
  if i.val<l then padDemand n i.val else min (padDemand n i.val) (padDemand R (i.val-l))

theorem protected_original_bound {s t:ℕ} (n:Fin s→ℕ) (R:Fin t→ℕ) (l j:ℕ) :
    padDemand (protectedDemand n R l) j≤padDemand n j := by
  by_cases live:j<min s (t+l)
  · rw [padDemand,dif_pos live]
    dsimp only [protectedDemand];split_ifs <;> omega
  · rw [padDemand,dif_neg live];omega

theorem protected_restored_bound {s t:ℕ} (n:Fin s→ℕ) (R:Fin t→ℕ) (l j:ℕ) :
    padDemand (protectedDemand n R l) (j+l)≤padDemand R j := by
  by_cases live:j+l<min s (t+l)
  · rw [padDemand,dif_pos live]
    simp only [protectedDemand,show ¬j+l<l by omega,if_false,Nat.add_sub_cancel]
    exact Nat.min_le_right _ _
  · rw [padDemand,dif_neg live];omega

theorem protected_demand_antitone {s t:ℕ} (n:Fin s→ℕ) (R:Fin t→ℕ) (hn:Antitone n) (hr:Antitone R) (l:ℕ) :
    Antitone (protectedDemand n R l) := by
  intro i j le
  have order : i.val≤j.val := le
  have original := pad_antitone n hn order
  have residual := pad_antitone R hr (Nat.sub_le_sub_right order l)
  dsimp only [protectedDemand];split_ifs <;> omega

theorem protected_demand_positive {s t:ℕ} (n:Fin s→ℕ) (R:Fin t→ℕ) (pn:∀i,1≤n i) (pr:∀j,1≤R j)
    (l:ℕ) (i:Fin (min s (t+l))) : 1≤protectedDemand n R l i := by
  have idx := i.isLt
  have orig := pad_positive n pn i.val (by omega)
  unfold protectedDemand;split_ifs
  · exact orig
  · exact le_min orig (pad_positive R pr _ (by omega))

theorem protected_demand_threshold {s t:ℕ} (n:Fin s→ℕ) (R:Fin t→ℕ) (hn:Antitone n) (hr:Antitone R) (l h:ℕ) :
    originalThresholdCount (protectedDemand n R l) h=min (originalThresholdCount n h) (originalThresholdCount R h+l) := by
  let K := protectedDemand n R l
  let f := originalThresholdCount n h
  let g := originalThresholdCount R h
  let p := originalThresholdCount K h
  have fs : f≤s := original_threshold_le_length n h
  have gt : g≤t := original_threshold_le_length R h
  have room : p≤min s (t+l) := original_threshold_le_length K h
  have characterized (i:Fin (min s (t+l))) : i.val<p ↔ i.val<min f (g+l) := by
    rw [←original_threshold_prefix K (protected_demand_antitone n R hn hr l)]
    have fits := i.isLt
    have idx : i.val<s := by omega
    have a := original_threshold_prefix n hn h ⟨i.val,idx⟩
    change h≤n ⟨i.val,idx⟩ ↔ i.val<f at a
    dsimp only [K,protectedDemand]
    rw [show padDemand n i.val=n ⟨i.val,idx⟩ from dif_pos idx]
    split_ifs with early
    · omega
    · have jr : i.val-l<t := by omega
      rw [show padDemand R (i.val-l)=R ⟨i.val-l,jr⟩ from dif_pos jr]
      have b := original_threshold_prefix R hr h ⟨i.val-l,jr⟩
      change h≤R ⟨i.val-l,jr⟩ ↔ i.val-l<g at b
      omega
  change p=min f (g+l)
  by_contra ne
  let i : Fin (min s (t+l)) := ⟨min p (min f (g+l)),by omega⟩
  have agrees := characterized i
  change min p (min f (g+l))<p ↔ min p (min f (g+l))<min f (g+l) at agrees
  omega

#print axioms protected_original_bound
#print axioms protected_restored_bound
#print axioms protected_demand_antitone
#print axioms protected_demand_positive
#print axioms protected_demand_threshold
end JSP452Audit.StarHost
