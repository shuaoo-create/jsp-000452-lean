import TheCommonIntegralAssignmentsRealizeTheScaledOptimalResource
namespace JSP452Audit.StarHost.DegreeRegion
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D:ℕ} (K:DegreeRegion G D)
def actualLink (r:X) (c:K.pieces) := originalPortIncidence G K.barrier r c.val

theorem actual_link_neighbors (T:Set K.pieces) :
    rootNeighbors K.actualLink T=regionRoots G K.barrier (Subtype.val '' T) := by
  rw [←neighboring_roots_are_original_labels]
  ext x;constructor
  · rintro ⟨c,ct,e⟩;exact ⟨c.val,⟨c,ct,rfl⟩,e⟩
  · rintro ⟨c,⟨z,zt,rfl⟩,e⟩;exact ⟨z,zt,e⟩

theorem original_roots_seed_the_scaled_problem :
    ∃P:RootAllocation G K.barrier,
      (∀a:K.barrier,P.place a∈K.pieces ↔ a.val∈K.roots) ∧
      K.pieces\Set.range P.place=freeFull G K.barrier D P ∧
      ∃f:↥K.roots↪↥K.pieces,∀r,K.actualLink r.val (f r) := by
  obtain ⟨_,P,opt⟩ := allocation_exposure_exact G K.barrier K.tight K.critical D
  obtain ⟨sat,free⟩ := attaining_neighborhood_saturated G K.barrier D P K.pieces K.full opt K.balanced
  have test (a:K.barrier) : P.place a∈K.pieces ↔ a.val∈K.roots := by
    constructor
    · intro hit;exact ⟨a,sat ▸ (show a∈{r:K.barrier|P.place r∈K.pieces} from hit),rfl⟩
    · rintro ⟨b,used,e⟩
      have eq:b=a := Subtype.ext e
      have started : b∈{r:K.barrier|P.place r∈K.pieces} := sat.symm ▸ used
      exact eq ▸ started
  have inside (r:K.roots) : r.val∈K.barrier := by
    obtain ⟨a,_,e⟩ := r.property;exact e ▸ a.property
  let root (r:K.roots) : K.barrier := ⟨r.val,inside r⟩
  let seed (r:K.roots) : K.pieces := ⟨P.place (root r),(test _).2 r.property⟩
  have distinct : Function.Injective seed := by
    intro a b eq
    have same : P.place (root a)=P.place (root b) := congrArg Subtype.val eq
    exact Subtype.ext (congrArg (fun v:K.barrier => v.val) (P.place.injective same))
  exact ⟨P,test,free,⟨seed,distinct⟩,fun r => ⟨inside r,P.link (root r)⟩⟩

#print axioms actual_link_neighbors
#print axioms original_roots_seed_the_scaled_problem
end JSP452Audit.StarHost.DegreeRegion
