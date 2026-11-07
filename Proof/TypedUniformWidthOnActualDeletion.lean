import SixNoFiveStageIsRigid
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph

def ExactTypedWidth {X:Type*} (G:SimpleGraph X) (x y l:ℕ) : Prop := l=0 ∨
  ∃u v:ℕ,0<u ∧ 0<v ∧ u+v-1=l ∧ Forces G (forest (fun _:Fin u => x)) (forest (fun _:Fin v => y))

theorem palette_retains_typed_rectangle {X Y:Type*} [Finite X] (O:SimpleGraph X) (C:SimpleGraph Y)
    (P:SimpleGraph Y) (sub:P≤C) {s t r x y a b:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (rx:0<x) (byh:0<y) (red:UniformPackCap P x a)
    (blue:UniformPackCap (C \ P) y b) (liveR:a<originalThresholdCount n x) (liveB:b<originalThresholdCount m y)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    ExactTypedWidth O x y (originalThresholdCount n x+originalThresholdCount m y-1-r-a-b) := by
  let f := originalThresholdCount n x
  let g := originalThresholdCount m y
  change ExactTypedWidth O x y (f+g-1-r-a-b)
  by_cases dead : f+g-1-r≤a+b
  · exact Or.inl (by omega)
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
  exact Or.inr ⟨f-i-a,g-j-b,by omega,by omega,by omega,force⟩

theorem typed_width_after_deletion {X:Type*} [Finite X] (G:SimpleGraph X) (V:Set X)
    {x y l:ℕ} (rx:0<x) (byh:0<y) (width:ExactTypedWidth G x y l) :
    ExactTypedWidth (G.induce Vᶜ) x y (l-V.ncard) := by
  by_cases dead : l≤V.ncard
  · exact Or.inl (by omega)
  rcases width with zero|⟨u,v,hu,hv,wide,force⟩
  · omega
  let n := fun _:ℕ => x
  let m := fun _:ℕ => y
  have row : ForcingRow G u v n m 0 := (row_zero_iff G hu hv n m).mpr force
  have next := row_delete_set G V n m (antitone_const) (antitone_const) (fun _ _ => rx) (fun _ _ => byh) row
  let i := min V.ncard (u-1)
  let j := V.ncard-i
  have red : i<u := by dsimp [i];omega
  have blue : j<v := by dsimp [i,j];omega
  have index : i+j=0+V.ncard := by dsimp [i,j];omega
  have actual := next i j (u-i) (v-j) index (by omega) (by omega) (by omega) (by omega)
  exact Or.inr ⟨u-i,v-j,by omega,by omega,by omega,actual⟩

theorem sharp_five_from_typed_width {X:Type*} [Finite X] (G:SimpleGraph X) (cap:∀v,Nat.card (G.neighborSet v)≤5)
    (l:ℕ) (width:ExactTypedWidth G 4 3 l ∨ ExactTypedWidth G 3 4 l) :
    l+2*((l+1)/2)≤minimumExposure G 5 := by
  rcases width with (zero|⟨u,v,hu,hv,wide,force⟩)|(zero|⟨u,v,hu,hv,wide,force⟩)
  · simp [zero]
  · have bound := actual_five_sharp_signed_width G cap u v hu hv force;rwa [wide] at bound
  · simp [zero]
  · have bound := actual_five_sharp_signed_width G cap v u hv hu (forces_swap force);rwa [Nat.add_comm v u,wide] at bound

#print axioms palette_retains_typed_rectangle
#print axioms typed_width_after_deletion
#print axioms sharp_five_from_typed_width
end JSP452Audit.StarHost
