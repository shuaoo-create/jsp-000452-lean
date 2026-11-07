import ActualThresholdSubrectangle
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph

def UniformPackCap {X:Type*} (C:SimpleGraph X) (x a:ℕ) : Prop :=
  ∀k,(forest (fun _:Fin k => x)).IsContained C → k≤a

theorem residual_uniform_summand {X Y:Type*} (O:SimpleGraph X) (C:SimpleGraph Y) (x k a:ℕ)
    (cap:UniformPackCap C x a) (copy:(forest (fun _:Fin k => x)).IsContained (O⊕g C)) :
    (forest (fun _:Fin (k-a) => x)).IsContained O := by
  obtain ⟨l,q,sum,left,right⟩ := uniform_copy_split_sum O C x k copy
  have bound := cap q right
  obtain ⟨f⟩ := left
  exact ⟨f.comp (subforestCopy _ _ (Fin.castLEEmb (show k-a≤l by omega)) (fun _ => le_rfl))⟩

theorem palette_rectangle_tax {X Y:Type*} [Finite X] (O:SimpleGraph X) (C:SimpleGraph Y)
    (P:SimpleGraph Y) (sub:P≤C) {s t r x y a b:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (rx:0<x) (byh:0<y) (red:UniformPackCap P x a)
    (blue:UniformPackCap (C \ P) y b) (liveR:a<originalThresholdCount n x) (liveB:b<originalThresholdCount m y)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    originalThresholdCount n x+originalThresholdCount m y-1-r≤uniformEnvelope O (x+y-1)+a+b := by
  let f := originalThresholdCount n x
  let g := originalThresholdCount m y
  change f+g-1-r≤uniformEnvelope O (x+y-1)+a+b
  by_cases dead : f+g-1-r≤a+b
  · omega
  change a<f at liveR
  change b<g at liveB
  let i := min r (f-1-a)
  let j := r-i
  have index : i+j=r := by dsimp [i,j];omega
  have redLive : i+a<f := by dsimp [i];omega
  have blueLive : j+b<g := by dsimp [i,j];omega
  have source := uniform_rectangle_at (O⊕g C) n m hn hm index
    (show i<originalThresholdCount n x by change i<f;omega) (show j<originalThresholdCount m y by change j<g;omega) row
  have force : Forces O (forest (fun _:Fin (f-i-a) => x)) (forest (fun _:Fin (g-j-b) => y)) := by
    intro R less
    obtain ⟨both,comp⟩ := JSP452Audit.StarHost.sum_colors less sub
    rcases source _ both with first|second
    · exact Or.inl (residual_uniform_summand R P x (f-i) a red first)
    · rw [comp] at second
      exact Or.inr (residual_uniform_summand (O \ R) (C \ P) y (g-j) b blue second)
  have cert := uniform_pair_le_envelope O x y (f-i-a) (g-j-b) (x+y-1)
    rx byh (by omega) (by omega) rfl force
  omega

#print axioms residual_uniform_summand
#print axioms palette_rectangle_tax
end JSP452Audit.StarHost
