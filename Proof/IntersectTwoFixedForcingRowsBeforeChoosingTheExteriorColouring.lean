import OneProtectedListWithExactCumulativeCountsAtEveryOriginalHeight
namespace JSP452Audit.StarHost
open SimpleGraph

theorem weaken_original_suffix (f g:ℕ→ℕ) (i j u v:ℕ) (fit:u≤v) (heads:∀a<u,f (i+a)≤g (j+a)) :
    (suffixStars f i u).IsContained (suffixStars g j v) := by
  exact ⟨subforestCopy _ _ (Fin.castLEEmb fit) (fun a => heads a.val a.isLt)⟩

theorem intersect_two_fixed_rows {X:Type*} (Y:SimpleGraph X) {s t u v r:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ)
    (R:Fin u→ℕ) (T:Fin v→ℕ) (l:ℕ) (legal:l≤r+1)
    (first:ForcingRow Y u t (padDemand R) (padDemand m) r)
    (second:ForcingRow Y s v (padDemand n) (padDemand T) r) :
    ForcingRow Y (min s (u+l)) (min t (v+l)) (padDemand (protectedDemand n R l)) (padDemand (protectedDemand m T l)) (r+l) := by
  intro i j a b idx ra sb pa pb A sub
  by_cases right:l ≤ i
  · let z := i-l
    have origin : z+j=r := by dsimp only [z];omega
    have ix : z+(u-z)=u := by dsimp only [z];omega
    have jx : j+(t-j)=t := by omega
    have roomA : a≤u-z := by dsimp only [z];omega
    have roomB : b≤t-j := by omega
    have red := weaken_original_suffix (padDemand (protectedDemand n R l)) (padDemand R) i z a (u-z) roomA (by
      intro w _;rw [show i+w=z+w+l by dsimp only [z];omega];exact protected_restored_bound n R l _)
    have blue := weaken_original_suffix (padDemand (protectedDemand m T l)) (padDemand m) j j b (t-j) roomB
      (fun w _ => protected_original_bound m T l _)
    rcases first z j (u-z) (t-j) origin ix jx (by omega) (by omega) A sub with found|found
    · exact Or.inl (red.trans found)
    · exact Or.inr (blue.trans found)
  · let w := j-l
    have origin : i+w=r := by dsimp only [w];omega
    have ix : i+(s-i)=s := by omega
    have jx : w+(v-w)=v := by dsimp only [w];omega
    have roomA : a≤s-i := by omega
    have roomB : b≤v-w := by dsimp only [w];omega
    have red := weaken_original_suffix (padDemand (protectedDemand n R l)) (padDemand n) i i a (s-i) roomA
      (fun z _ => protected_original_bound n R l _)
    have blue := weaken_original_suffix (padDemand (protectedDemand m T l)) (padDemand T) j w b (v-w) roomB (by
      intro z _;rw [show j+z=w+z+l by dsimp only [w];omega];exact protected_restored_bound m T l _)
    rcases second i w (s-i) (v-w) origin ix jx (by omega) (by omega) A sub with found|found
    · exact Or.inl (red.trans found)
    · exact Or.inr (blue.trans found)

#print axioms weaken_original_suffix
#print axioms intersect_two_fixed_rows
end JSP452Audit.StarHost
