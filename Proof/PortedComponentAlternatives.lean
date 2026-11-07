import OddGoodFullCovered
import GoodPortClassification

namespace JSP452Audit.StarHost
open SimpleGraph

/-- The excluded components are components of the original host itself. -/
def NoOriginalRegularCritical {X : Type*} (G : SimpleGraph X) (D : ℕ) : Prop :=
  ∀ d : G.ConnectedComponent, (∀ x : d.supp, Nat.card (d.toSimpleGraph.neighborSet x)=D) →
    ¬ PerfectAfterEveryDeletion d.toSimpleGraph

theorem perfect_after_deletion_of_iso {X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    (e : G ≃g H) (critical : PerfectAfterEveryDeletion G) : PerfectAfterEveryDeletion H := by
  intro y
  let x := e.symm y
  have sends : e x=y := e.apply_symm_apply y
  have cuts : Set.BijOn (⇑e) {z | z≠x} {w | w≠y} := by
    refine ⟨?_,e.injective.injOn,?_⟩
    · intro z hz same; exact hz (e.injective (same.trans sends.symm))
    · intro w hw
      refine ⟨e.symm w,?_,e.apply_symm_apply _⟩
      intro same; exact hw (e.symm.injective same)
  let f := e.induce cuts
  obtain ⟨M,perf⟩ := critical x
  refine ⟨M.map f.toHom,perf.1.map f.toHom f.injective,?_⟩
  intro w
  obtain ⟨v,rfl⟩ := f.surjective w
  exact ⟨v,perf.2 v,rfl⟩

/-- If all original and internal degrees already equal D, the component has
used every original edge at each of its vertices. Hence the original component
of any anchor consists of exactly those same labels. -/
theorem regular_barrier_component_lifts {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (D : ℕ) (c : (G.induce Sᶜ).ConnectedComponent) (full : allFullComponent G S D c)
    (regular : ∀ x : c.supp, Nat.card (c.toSimpleGraph.neighborSet x)=D)
    (critical : PerfectAfterEveryDeletion c.toSimpleGraph) (anchor : c.supp) :
    let d := G.connectedComponentMk anchor.val.val
    Subtype.val '' c.supp = d.supp ∧
      (∃ e : c.toSimpleGraph ≃g d.toSimpleGraph, ∀ x, (e x).val=x.val.val) ∧
      (∀ x : d.supp, Nat.card (d.toSimpleGraph.neighborSet x)=D) ∧
      PerfectAfterEveryDeletion d.toSimpleGraph := by
  classical
  intro d
  let label (v : c.supp) := v.val.val
  have inj : Function.Injective label := fun _ _ h => Subtype.ext (Subtype.ext h)
  have neigh (v : c.supp) : label '' c.toSimpleGraph.neighborSet v = G.neighborSet (label v) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro _ ⟨w,edge,rfl⟩; exact edge
    · rw [Set.ncard_image_of_injective _ inj,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,regular]
      exact (full v).le
  have supported (v : c.supp) : label v ∈ d.supp := by
    have reach := c.reachable_of_mem_supp v.property anchor.property
    exact ConnectedComponent.sound (reach.map (Embedding.induce (G:=G) Sᶜ).toHom)
  have support : Subtype.val '' c.supp = d.supp := by
    apply Set.Subset.antisymm
    · rintro _ ⟨v,hv,rfl⟩; exact supported ⟨v,hv⟩
    · intro w hw
      have reach := d.reachable_of_mem_supp (supported anchor) hw
      rw [reachable_iff_reflTransGen] at reach
      clear hw
      induction reach with
      | refl => exact ⟨anchor.val,anchor.property,rfl⟩
      | @tail a b _ edge ih =>
        obtain ⟨v,hv,rfl⟩ := ih
        let t : c.supp := ⟨v,hv⟩
        have member : b∈G.neighborSet (label t) := edge
        rw [← neigh t] at member
        obtain ⟨w,_,same⟩ := member
        exact ⟨w.val,w.property,same⟩
  let move (v : c.supp) : d.supp := ⟨label v,supported v⟩
  have bij : Function.Bijective move := by
    refine ⟨fun _ _ h => inj (congrArg (fun w : d.supp => w.val) h),?_⟩
    intro w
    obtain ⟨v,hv,same⟩ := (show w.val ∈ Subtype.val '' c.supp from support.symm ▸ w.property)
    exact ⟨⟨v,hv⟩,Subtype.ext same⟩
  let e : c.toSimpleGraph ≃g d.toSimpleGraph := {
    toEquiv := Equiv.ofBijective move bij
    map_rel_iff' := Iff.rfl }
  refine ⟨support,⟨e,fun _ => rfl⟩,?_,perfect_after_deletion_of_iso e critical⟩
  intro w
  obtain ⟨v,rfl⟩ := e.surjective w
  exact (Nat.card_congr (e.mapNeighborSet v)).symm.trans (regular v)

/-- After excluding regular critical components of the original graph, only the
odd clique and mixed good-port alternatives of the local classification remain. -/
theorem ported_component_alternatives {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (D : ℕ) (cap : ∀ x, Nat.card (G.neighborSet x)≤D)
    (noOriginal : NoOriginalRegularCritical G D)
    (c : (G.induce Sᶜ).ConnectedComponent) (full : allFullComponent G S D c)
    (critical : PerfectAfterEveryDeletion c.toSimpleGraph) (good : internallyGood c.toSimpleGraph D) :
    (c.toSimpleGraph=⊤ ∧ Odd (Nat.card c.supp) ∧ Nat.card c.supp≤D) ∨
      GoodPortSplit c.toSimpleGraph D := by
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  have bound (x : c.supp) : Nat.card (c.toSimpleGraph.neighborSet x) ≤ D :=
    (induced_neighbor_count_le _ c.supp x).trans ((induced_neighbor_count_le G Sᶜ x.val).trans (cap _))
  rcases good_port_classification c.toSimpleGraph D bound critical good with reg | rest
  · let v := c.nonempty_supp.to_subtype.some
    obtain ⟨_,_,regHost,critHost⟩ := regular_barrier_component_lifts G S D c full reg critical v
    exact (noOriginal _ regHost critHost).elim
  · exact rest

theorem DegreeRegion.ported_piece_alternatives {X : Type*} [Finite X] {G : SimpleGraph X} {D : ℕ}
    (K : DegreeRegion G D) (cap : ∀ x, Nat.card (G.neighborSet x)≤D)
    (noOriginal : NoOriginalRegularCritical G D) (c : (G.induce K.barrierᶜ).ConnectedComponent)
    (inside : c∈K.pieces) (good : internallyGood c.toSimpleGraph D) :
    (c.toSimpleGraph=⊤ ∧ Odd (Nat.card c.supp) ∧ Nat.card c.supp≤D) ∨
      GoodPortSplit c.toSimpleGraph D :=
  ported_component_alternatives G K.barrier D cap noOriginal c (K.full inside) (K.critical c).2 good

#print axioms regular_barrier_component_lifts
#print axioms ported_component_alternatives
#print axioms DegreeRegion.ported_piece_alternatives
end JSP452Audit.StarHost
