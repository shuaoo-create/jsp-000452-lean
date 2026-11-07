import NineErasureDegreeInventory
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph

structure ThreeDegreeStages {X : Type*} [Finite X] (G : SimpleGraph X) (p : ℕ) where
  upper : Set X
  first : CompleteDegreeStage G (p+2) upper
  middle : Set ↥(upperᶜ : Set X)
  second : CompleteDegreeStage (G.induce upperᶜ) (p+1) middle
  lower : Set ↥((nestedRemoved upper middle)ᶜ : Set X)
  third : CompleteDegreeStage (G.induce (nestedRemoved upper middle)ᶜ) p lower

theorem three_degree_stages_exist {X : Type*} [Finite X] (G : SimpleGraph X) (p : ℕ) :
    Nonempty (ThreeDegreeStages G p) := by
  obtain ⟨B,first⟩ := complete_degree_stage_exists G (p+2)
  obtain ⟨C,second⟩ := complete_degree_stage_exists (G.induce Bᶜ) (p+1)
  obtain ⟨A,third⟩ := complete_degree_stage_exists (G.induce (nestedRemoved B C)ᶜ) p
  exact ⟨⟨B,first,C,second,A,third⟩⟩

namespace ThreeDegreeStages
variable {X : Type*} [Finite X] {G : SimpleGraph X} {p : ℕ} (H : ThreeDegreeStages G p)
abbrev midCut := nestedRemoved H.upper H.middle
abbrev lastCut := nestedRemoved H.midCut H.lower

theorem degree_caps (cap : ∀v,Nat.card (G.neighborSet v)≤p+2) :
    (∀v,Nat.card ((G.induce H.upperᶜ).neighborSet v)≤p+1) ∧
    (∀v,Nat.card ((G.induce H.midCutᶜ).neighborSet v)≤p) ∧
    (∀v,Nat.card ((G.induce H.lastCutᶜ).neighborSet v)<p) := by
  have one (v) : Nat.card ((G.induce H.upperᶜ).neighborSet v)≤p+1 := by
    have := complete_stage_lowers_cap G (p+2) H.upper cap H.first v
    omega
  have next := complete_stage_lowers_cap _ (p+1) H.middle one H.second
  have mid := nested_deletion_cap G H.upper H.middle p (fun v => by have := next v;omega)
  have last := complete_stage_lowers_cap (G.induce H.midCutᶜ) p H.lower mid H.third
  have iso := nestedDeletionIso G H.midCut H.lower
  refine ⟨one,mid,fun v => ?_⟩
  let x := iso.symm v
  have bound := last x
  have same := Nat.card_congr (iso.mapNeighborSet x)
  change Nat.card (((G.induce H.midCutᶜ).induce H.lowerᶜ).neighborSet x)=
    Nat.card ((G.induce H.lastCutᶜ).neighborSet (iso x)) at same
  rw [iso.apply_symm_apply v] at same
  exact same ▸ bound

theorem exact_last_prefix (k : ℕ) (short : H.midCut.ncard<k) (fits : k≤H.lastCut.ncard) :
    ∃V : Set X,V.ncard=k ∧
      G.edgeSet.ncard=(G.induce Vᶜ).edgeSet.ncard+p*k+H.upper.ncard+H.midCut.ncard := by
  have count := nested_removed_card H.midCut H.lower
  change H.lastCut.ncard=H.midCut.ncard+H.lower.ncard at count
  obtain ⟨U,_,size,part⟩ := subset_of_stage_price _ p H.lower H.third (k-H.midCut.ncard) (by omega)
  let V := nestedRemoved H.midCut U
  have sz := nested_removed_card H.midCut U
  change V.ncard=H.midCut.ncard+U.ncard at sz
  have mid := nested_removed_card H.upper H.middle
  change H.midCut.ncard=H.upper.ncard+H.middle.ncard at mid
  have cost1 := JSP452Audit.StarHost.degree_on_independent_full_set G H.upper (p+2) H.first.2.1 H.first.1
  have cost2 := JSP452Audit.StarHost.degree_on_independent_full_set _ H.middle (p+1) H.second.2.1 H.second.1
  have after2 := nested_deletion_edges G H.upper H.middle
  change _=(G.induce H.midCutᶜ).edgeSet.ncard at after2
  have after3 := nested_deletion_edges G H.midCut U
  change _=(G.induce Vᶜ).edgeSet.ncard at after3
  rw [after2] at cost2
  rw [after3] at part
  have sum : p*k=p*H.upper.ncard+p*H.middle.ncard+p*(k-H.midCut.ncard) := by
    rw [←Nat.mul_add,←Nat.mul_add];congr 1;omega
  refine ⟨V,by omega,?_⟩
  rw [sum]
  rw [Nat.add_mul] at cost1 cost2
  change (G.induce H.midCutᶜ).edgeSet.ncard=(G.induce Vᶜ).edgeSet.ncard+p*(k-H.midCut.ncard) at part
  omega

#print axioms degree_caps
#print axioms exact_last_prefix
end ThreeDegreeStages
#print axioms three_degree_stages_exist
end JSP452Audit.StarHost
