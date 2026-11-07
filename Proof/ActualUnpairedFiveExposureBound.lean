import TwoSafeLabelClasses
namespace JSP452Audit.StarHost.FiveExposureLabels
open SimpleGraph
variable {X:Type*} [Finite X] {G:SimpleGraph X} (L:FiveExposureLabels G)

theorem actual_unpaired_label_split (cap:∀v,Nat.card (G.neighborSet v)≤5) :
    ∃R:SimpleGraph X,R≤L.base ∧ ∃A:Set ↥L.W,
      (∀v,(R.neighborSet v).ncard+(L.fiber A v).ncard≤2) ∧
      (∀v,((L.base \ R).neighborSet v).ncard+(L.fiber Aᶜ v).ncard≤2) := by
  classical
  have budget := L.residual_degree_with_ports cap
  have low (v:X) : Nat.card (L.base.neighborSet v)≤2*(1+1) := (Nat.le_add_right _ _).trans (budget v)
  obtain ⟨R,sub,split⟩ := even_even_degree_split L.base 1 1 low
  let B := L.base \ R
  let total (v:X) := L.fiber Set.univ v
  let take (v:X) := min (total v).ncard (2-(R.neighborSet v).ncard)
  have pick (v:X) : ∃S:Set ↥L.W,S⊆total v ∧ S.ncard=take v := Set.exists_subset_card_eq (Nat.min_le_left _ _)
  choose S subset sizes using pick
  let A := {u:↥L.W | u∈S (L.tip u)}
  have same (v:X) : L.fiber A v=S v := by
    ext u
    constructor
    · rintro ⟨mem,eq⟩
      change u∈S (L.tip u) at mem;rwa [eq] at mem
    · intro mem
      have eq := (subset v mem).2
      exact ⟨by change u∈S (L.tip u);rw [eq];exact mem,eq⟩
  have other (v:X) : L.fiber Aᶜ v=total v\S v := by
    ext u
    constructor
    · rintro ⟨away,eq⟩
      exact ⟨⟨Set.mem_univ _,eq⟩,fun mem => away (show u∈S (L.tip u) from eq ▸ mem)⟩
    · rintro ⟨⟨_,eq⟩,away⟩
      exact ⟨fun mem => away ((show L.tip u=v from eq) ▸ (show u∈S (L.tip u) from mem)),eq⟩
  have combined (v:X) : (R.neighborSet v).ncard+(B.neighborSet v).ncard=(L.base.neighborSet v).ncard := by
    have dis : Disjoint (R.neighborSet v) (B.neighborSet v) := Set.disjoint_left.mpr fun _ e h => h.2 e
    have union : R.neighborSet v∪B.neighborSet v=L.base.neighborSet v := by
      ext w
      exact ⟨fun h => h.elim (fun e => sub e) (fun e => e.1),fun e =>
        by by_cases r:R.Adj v w;exact Or.inl r;exact Or.inr ⟨e,r⟩⟩
    exact (Set.ncard_union_eq dis).symm.trans (congrArg Set.ncard union)
  refine ⟨R,sub,A,?_,?_⟩
  · intro v
    rw [same,sizes]
    have small : (R.neighborSet v).ncard≤2 := (split v).1
    dsimp [take];omega
  · intro v
    have old := budget v
    change (L.base.neighborSet v).ncard+(total v).ncard≤4 at old
    have sum := combined v
    have first : (R.neighborSet v).ncard≤2 := (split v).1
    have second : (B.neighborSet v).ncard≤2 := (split v).2
    have count := Set.ncard_sdiff_add_ncard_of_subset (subset v)
    change (B.neighborSet v).ncard+(L.fiber Aᶜ v).ncard≤2
    rw [other]
    rw [sizes] at count
    dsimp only [take] at count
    omega

end JSP452Audit.StarHost.FiveExposureLabels
namespace JSP452Audit.StarHost
open SimpleGraph
theorem actual_five_double_signed_width {X:Type*} [Finite X] (G:SimpleGraph X)
    (cap:∀v,Nat.card (G.neighborSet v)≤5) (u v:ℕ) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => 4)) (forest (fun _:Fin v => 3))) :
    2*(u+v-1)≤minimumExposure G 5 := by
  obtain ⟨L⟩ := five_exposure_labels_exist G
  obtain ⟨R,sub,A,red,blue⟩ := L.actual_unpaired_label_split cap
  obtain ⟨a,b⟩ := L.two_safe_classes_large R sub A red blue u v hu hv force
  have size := Set.ncard_add_ncard_compl A
  change A.ncard+Aᶜ.ncard=L.W.ncard at size
  have eq : L.W.ncard=minimumExposure G 5 := L.optimal
  omega

#print axioms FiveExposureLabels.actual_unpaired_label_split
#print axioms actual_five_double_signed_width
end JSP452Audit.StarHost
