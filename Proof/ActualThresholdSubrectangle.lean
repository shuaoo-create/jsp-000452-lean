import ActualSixComponentsNearPerfect
namespace JSP452Audit.StarHost
open SimpleGraph

theorem uniform_inside_original_suffix {s i l u x:ℕ} (n:Fin s→ℕ) (hn:Antitone n)
    (len:i+l=s) (fit:i+u≤originalThresholdCount n x) :
    (forest (fun _:Fin u => x)).IsContained (suffixStars (padDemand n) i l) := by
  have bound := original_threshold_le_length n x
  let labels : Fin u ↪ Fin l := Fin.castLEEmb (by omega)
  refine ⟨subforestCopy _ _ labels ?_⟩
  intro a
  let idx : Fin s := ⟨i+a.val,by have := a.isLt;omega⟩
  have height := (original_threshold_prefix n hn x idx).2 (by change i+a.val<originalThresholdCount n x;have := a.isLt;omega)
  change x≤padDemand n (i+a.val)
  rwa [show padDemand n (i+a.val)=n idx from dif_pos idx.isLt]

theorem uniform_rectangle_at (G:SimpleGraph X) {s t r i j x y:ℕ}
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (ij:i+j=r) (red:i<originalThresholdCount n x) (blue:j<originalThresholdCount m y)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    Forces G (forest (fun _:Fin (originalThresholdCount n x-i) => x)) (forest (fun _:Fin (originalThresholdCount m y-j) => y)) := by
  have ncap := original_threshold_le_length n x
  have mcap := original_threshold_le_length m y
  have actual := row i j (s-i) (t-j) ij (by omega) (by omega) (by omega) (by omega)
  intro R sub
  rcases actual R sub with first|second
  · obtain ⟨rc⟩ := first
    obtain ⟨e⟩ := uniform_inside_original_suffix (x:=x) (i:=i) (u:=originalThresholdCount n x-i) n hn
      (show i+(s-i)=s by omega) (by omega)
    exact Or.inl ⟨rc.comp e⟩
  · obtain ⟨bc⟩ := second
    obtain ⟨e⟩ := uniform_inside_original_suffix (x:=y) (i:=j) (u:=originalThresholdCount m y-j) m hm
      (show j+(t-j)=t by omega) (by omega)
    exact Or.inr ⟨bc.comp e⟩

#print axioms uniform_inside_original_suffix
#print axioms uniform_rectangle_at
end JSP452Audit.StarHost
