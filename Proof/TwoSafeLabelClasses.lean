import SafeLabelPaletteRestoration
namespace JSP452Audit.StarHost.FiveExposureLabels
open SimpleGraph
variable {X:Type*} [Finite X] {G:SimpleGraph X} (L:FiveExposureLabels G)

theorem two_safe_classes_large (R:SimpleGraph X) (sub:R≤L.base) (A:Set ↥L.W)
    (red:∀v,(R.neighborSet v).ncard+(L.fiber A v).ncard≤2)
    (blue:∀v,((L.base \ R).neighborSet v).ncard+(L.fiber Aᶜ v).ncard≤2)
    (u v:ℕ) (hu:0<u) (hv:0<v) (force:Forces G (forest (fun _:Fin u => 4)) (forest (fun _:Fin v => 3))) :
    u+v-1≤A.ncard ∧ u+v-1≤Aᶜ.ncard := by
  have capR (x:X) : Nat.card (R.neighborSet x)≤2 := (Nat.le_add_right _ _).trans (red x)
  have capB (x:X) : Nat.card ((L.base \ R).neighborSet x)≤2 := (Nat.le_add_right _ _).trans (blue x)
  have first := L.actual_labels_force_complement R sub A red capB u v hu hv force
  have invol : L.base \ (L.base \ R)=R := by
    ext x y
    change (L.base.Adj x y ∧ ¬(L.base.Adj x y ∧ ¬R.Adj x y)) ↔ R.Adj x y
    have incl : R.Adj x y → L.base.Adj x y := fun e => sub e
    tauto
  have other := L.actual_labels_force_complement (L.base \ R) sdiff_le Aᶜ blue (by rw [invol];exact capR) u v hu hv force
  exact ⟨by simpa only [compl_compl] using other,first⟩

theorem paired_label_exposure_bound (R:SimpleGraph X) (sub:R≤L.base) (A:Set ↥L.W)
    (red:∀v,(R.neighborSet v).ncard+(L.fiber A v).ncard≤2)
    (blue:∀v,((L.base \ R).neighborSet v).ncard+(L.fiber Aᶜ v).ncard≤2)
    (evenSide:Even A.ncard ∨ Even Aᶜ.ncard) (u v:ℕ) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => 4)) (forest (fun _:Fin v => 3))) :
    let l := u+v-1
    l+2*((l+1)/2)≤minimumExposure G 5 := by
  intro l
  obtain ⟨a,b⟩ := L.two_safe_classes_large R sub A red blue u v hu hv force
  change l≤A.ncard at a
  change l≤Aᶜ.ncard at b
  have total := Set.ncard_add_ncard_compl A
  change A.ncard+Aᶜ.ncard=L.W.ncard at total
  have exactSize : L.W.ncard=minimumExposure G 5 := L.optimal
  rcases evenSide with ⟨q,eq⟩|⟨q,eq⟩ <;> omega

#print axioms two_safe_classes_large
#print axioms paired_label_exposure_bound
end JSP452Audit.StarHost.FiveExposureLabels
