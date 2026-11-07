import ErasedSuffixThresholdLabels
namespace JSP452Audit.StarHost
open SimpleGraph

/-- The two lower bounds are realized within one fixed surviving star
list by distinct component labels. They may be joined positionwise. -/
theorem join_same_survivor {s i l old a μ : ℕ} (n : Fin s→ℕ) (hn : Antitone n)
    (W : RemovalBudget s) (length : i+old=s) (fits : i+l=W.len)
    (U : Set (Fin old)) [Fintype U] (legal : originalRemoved i old length.le Uᶜ∈W.choices)
    (v : U→ℕ) (positive : ∀z,1≤v z) (touch : Finset (Fin old)) (budget : touch.card≤μ)
    (keep : ∀z:Fin old,z∉touch → z∈U)
    (same : ∀z:U,z.val∉touch → v z=n (originalSuffixLabel i old length.le z.val))
    (shortened : Finset U) (roots : shortened.card≤a)
    (undamaged : ∀z:U,z∉shortened → v z=n (originalSuffixLabel i old length.le z.val)) :
    (suffixStars (padDemand (commonErasedDemand n W a μ)) i l).IsContained (forest v) := by
  classical
  obtain ⟨g,quality⟩ := retained_budget_indices n W length fits U legal
  let small (k:Fin l) := padDemand (commonErasedDemand n W a μ) (i+k.val)
  have room (k:Fin l) : i+k.val<W.len := by have := k.isLt;omega
  have enough (k:Fin l) : k.val+1≤(Finset.univ.filter (fun z:U => small k≤v z)).card := by
    let h := small k
    have val : h=max (max 1 (padDemand (W.entries n) (i+k.val+a))) (padDemand n (i+k.val+μ)) := by
      change padDemand (commonErasedDemand n W a μ) (i+k.val)=_
      rw [padDemand,dif_pos (room k)];rfl
    change k.val+1≤(Finset.univ.filter (fun z:U => h≤v z)).card
    by_cases unit : h≤1
    · have all : (Finset.univ.filter (fun z:U => h≤v z))=Finset.univ :=
        Finset.filter_true_of_mem (fun z _ => unit.trans (positive z))
      have card := Fintype.card_le_of_injective g g.injective
      rw [all,Finset.card_univ];simp only [Fintype.card_fin] at card;have := k.isLt;omega
    by_cases viaL : h≤padDemand (W.entries n) (i+k.val+a)
    · have inside : i+k.val+a<W.len := by
        by_contra no;rw [padDemand,dif_neg no] at viaL;omega
      let q := a+k.val+1
      let part : Fin q ↪ Fin l := Fin.castLEEmb (by dsimp [q];omega)
      have fit (z:Fin q) (ok:g (part z)∉shortened) : h≤v (g (part z)) := by
        rw [undamaged _ ok]
        have first := quality (part z)
        have order : i+(part z).val≤ i+k.val+a := by change i+z.val≤ i+k.val+a;have := z.isLt;dsimp [q] at *;omega
        exact viaL.trans ((pad_antitone _ (W.entries_antitone n hn) order).trans first)
      have count := many_after_exceptions (part.trans g) shortened roots v h fit
      change q-a≤_ at count;dsimp [q] at count;omega
    · have viaN : h≤padDemand n (i+k.val+μ) := by omega
      have inside : i+k.val+μ<s := by
        by_contra no;rw [padDemand,dif_neg no] at viaN;omega
      let q := μ+k.val+1
      let part : Fin q ↪ Fin old := Fin.castLEEmb (by dsimp [q];omega)
      have fit (z:Fin q) (ok:part z∉touch) : h≤v ⟨part z,keep _ ok⟩ := by
        rw [same ⟨part z,keep _ ok⟩ ok]
        rw [padDemand,dif_pos inside] at viaN
        apply viaN.trans (hn ?_)
        change i+z.val≤ i+k.val+μ
        have := z.isLt;dsimp [q] at *;omega
      have count := many_in_retained_subtype part touch budget U v h (fun z => keep (part z)) fit
      change q-μ≤_ at count;dsimp [q] at count;omega
  obtain ⟨idx,fit⟩ := labels_of_thresholds small v enough
  exact ⟨subforestCopy small v idx fit⟩

#print axioms join_same_survivor
end JSP452Audit.StarHost
