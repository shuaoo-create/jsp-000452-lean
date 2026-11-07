import ActualCommonUnpaidHeight
namespace JSP452Audit.StarHost

theorem common_demand_le_residual {s : ℕ} (n : Fin s→ℕ) (hn : Antitone n) (pn:∀i,1≤n i)
    (W : RemovalBudget s) (a μ : ℕ) (fit : W.loss≤μ) (i : Fin W.len) :
    commonErasedDemand n W a μ i≤W.entries n i := by
  have cap := pad_antitone (W.entries n) (W.entries_antitone n hn) (show i.val≤ i.val+a by omega)
  rw [show padDemand (W.entries n) i.val=W.entries n i from dif_pos i.isLt] at cap
  have shift := residual_dominates_shift W n hn i
  have original := pad_antitone n hn (show W.loss+i.val≤ i.val+μ by omega)
  exact max_le (max_le (W.entries_positive n pn i) cap) (original.trans shift)

theorem height_count_mono {s : ℕ} {n m : Fin s→ℕ} (le : ∀i,n i≤m i) (h : ℕ) :
    originalThresholdCount n h≤originalThresholdCount m h := by
  apply Finset.card_le_card
  exact fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.trans (le i)⟩

/-- The complete exterior loses at most e0 occurrences of any original
threshold; the retained-root graph loses at most mu, and at most a from L. -/
theorem common_threshold_floors {s : ℕ} (n : Fin s→ℕ) (hn : Antitone n) (pn:∀i,1≤n i)
    (W : RemovalBudget s) (a μ h : ℕ) (fit : W.loss≤μ) :
    let L := W.entries n
    let J := commonErasedDemand n W a μ
    originalThresholdCount n h≤W.loss+originalThresholdCount L h ∧
    originalThresholdCount n h≤μ+originalThresholdCount J h ∧
    originalThresholdCount L h≤a+originalThresholdCount J h ∧
    originalThresholdCount J h≤originalThresholdCount L h := by
  intro L J
  have lower := height_count_mono (fun i:Fin W.len => residual_dominates_shift W n hn i) h
  have shift := threshold_tail_count n hn W.loss h
  change originalThresholdCount (remainingDemand n W.loss) h ≤ originalThresholdCount L h at lower
  have one : originalThresholdCount n h≤W.loss+originalThresholdCount L h := by omega
  have jsmall := height_count_mono (common_demand_le_residual n hn pn W a μ fit) h
  change originalThresholdCount J h≤originalThresholdCount L h at jsmall
  have sa := original_threshold_le_length n h
  have sl := original_threshold_le_length L h
  let c := originalThresholdCount J h
  have antic := common_erased_antitone n hn W a μ
  refine ⟨one,?_,?_,jsmall⟩
  · change originalThresholdCount n h≤μ+c
    by_contra! fail
    have inL : c<W.len := by dsimp [RemovalBudget.len];omega
    let i : Fin W.len := ⟨c,inL⟩
    let z : Fin s := ⟨c+μ,by omega⟩
    have high := (original_threshold_prefix n hn h z).2 (by dsimp [z];omega)
    have post : h≤J i := by
      change h≤max _ (padDemand n (c+μ))
      rw [show padDemand n (c+μ)=n z from dif_pos z.isLt];exact high.trans (le_max_right _ _)
    have no := (original_threshold_prefix J antic h i).1 post
    exact (Nat.lt_irrefl c) no
  · change originalThresholdCount L h≤a+c
    by_contra! fail
    have inL : c<W.len := by omega
    let i : Fin W.len := ⟨c,inL⟩
    let j : Fin W.len := ⟨c+a,by omega⟩
    have high := (original_threshold_prefix L (W.entries_antitone n hn) h j).2 (by dsimp [j];omega)
    have post : h≤J i := by
      change h≤max (max 1 (padDemand L (c+a))) _
      rw [show padDemand L (c+a)=L j from dif_pos j.isLt]
      exact high.trans ((le_max_right 1 _).trans (le_max_left _ _))
    have no := (original_threshold_prefix J antic h i).1 post
    exact (Nat.lt_irrefl c) no

#print axioms common_demand_le_residual
#print axioms common_threshold_floors
end JSP452Audit.StarHost
