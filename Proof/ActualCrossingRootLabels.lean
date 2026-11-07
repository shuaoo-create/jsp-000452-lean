import SameCopyThresholdSelection
namespace JSP452Audit.StarHost
open SimpleGraph
variable {I X : Type*} [Finite X] {D : ℕ} (G : SimpleGraph X) (K : DegreeRegion G D)
variable (R : SimpleGraph X) (n : I→ℕ)
abbrev restoredInternal := G \ eraseInternal G K.core
variable (f : (forest n).Copy (R ⊔ restoredInternal G K))

def whollyInternal : Set I := {i | ∀j:Fin (n i+1),f ⟨i,j⟩∈K.core}

theorem actual_wholly_internal (less : R≤eraseInternal G K.core) :
    (forest (fun i:↥(whollyInternal G K R n f) => n i.val)).IsContained (G.induce K.core) := by
  let U := whollyInternal G K R n f
  let sel := subforestCopy (fun z:U => n z.val) n (Function.Embedding.subtype _) (fun _ => le_rfl)
  have sub : R⊔restoredInternal G K≤G := sup_le (less.trans (eraseInternal_le G K.core)) sdiff_le
  let g (z:Vertices (fun i:U => n i.val)) : K.core := ⟨f (sel z),z.1.property z.2⟩
  refine ⟨{toHom := { toFun := g,map_rel' := fun e => sub (f.toHom.map_adj (sel.toHom.map_adj e)) },
           injective' := fun _ _ h => sel.injective (f.injective (congrArg (fun z:K.core => z.val) h))}⟩

theorem wholly_internal_touched (less : R≤eraseInternal G K.core) (pn : ∀i,1≤n i) :
    whollyInternal G K R n f ⊆ touchedStars R (restoredInternal G K) n f := by
  intro i h
  let j : Fin (n i) := ⟨0,pn i⟩
  exact ⟨j,fun edge => (less edge).2 ⟨h 0,h j.succ⟩⟩

theorem touched_external_root_edge (less : R≤eraseInternal G K.core) {i:I} (outside : i∉whollyInternal G K R n f)
    (touch : i∈touchedStars R (restoredInternal G K) n f) :
    ∃j:Fin (n i), f (leaf n ⟨i,j⟩)∈K.roots ∧ R.Adj (f (center n i)) (f (leaf n ⟨i,j⟩)) := by
  obtain ⟨u,miss⟩ := touch
  have coreEdge := (f.toHom.map_adj (starEdge n ⟨i,u⟩)).resolve_left miss
  have centerCore : f (center n i)∈K.core := by
    by_contra notMem
    exact coreEdge.2 ⟨coreEdge.1,fun h => notMem h.1⟩
  have ext : ∃j:Fin (n i),f (leaf n ⟨i,j⟩)∉K.core := by
    by_contra! all
    exact outside (fun j => Fin.cases centerCore (fun b => all b) j)
  obtain ⟨j,away⟩ := ext
  have original := f.toHom.map_adj (starEdge n ⟨i,j⟩)
  have edge : R.Adj (f (center n i)) (f (leaf n ⟨i,j⟩)) := by
    rcases original with r|k
    · exact r
    · exact (k.2 ⟨k.1,fun h => away h.2⟩).elim
  have old := (less edge).1
  exact ⟨j,(regionCore_neighbor G K.barrier K.pieces centerCore old).resolve_right away,edge⟩

/-- Distinct shortened stars use distinct actual root labels. -/
theorem short_crossing_count (less : R≤eraseInternal G K.core) :
    (touchedStars R (restoredInternal G K) n f \ whollyInternal G K R n f).ncard≤K.roots.ncard := by
  let E := touchedStars R (restoredInternal G K) n f \ whollyInternal G K R n f
  let pick (i:E) := (touched_external_root_edge G K R n f less i.property.2 i.property.1).choose
  have root (i:E) : f (leaf n ⟨i.val,pick i⟩)∈K.roots :=
    (touched_external_root_edge G K R n f less i.property.2 i.property.1).choose_spec.1
  let send (i:E) : K.roots := ⟨_,root i⟩
  apply Nat.card_le_card_of_injective send
  intro i j eq
  have same := f.injective (congrArg (fun z:K.roots => z.val) eq)
  exact Subtype.ext (congrArg Sigma.fst same)

#print axioms actual_wholly_internal
#print axioms wholly_internal_touched
#print axioms touched_external_root_edge
#print axioms short_crossing_count
end JSP452Audit.StarHost
