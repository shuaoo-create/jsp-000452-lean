import ArbitraryOddClique
import CoreComponentSum
import PortedComponentAlternatives

namespace JSP452Audit.StarHost
open SimpleGraph

private def reserveComponentUnion {X : Type*} (G : SimpleGraph X)
    (T : Finset G.ConnectedComponent) : Set X :=
  {x | G.connectedComponentMk x ∈ T}

/-- The reserve of the actual induced union of any finite family of components
is at least the sum of their individual reserves. Empty unions are included. -/
theorem envelopeReserve_component_finset_le {X : Type*} [Finite X]
    (G : SimpleGraph X) (T : Finset G.ConnectedComponent) (k : ℕ) :
    (∑ c ∈ T, envelopeReserve c.toSimpleGraph k) ≤
      envelopeReserve (G.induce {x | G.connectedComponentMk x ∈ T}) k := by
  classical
  change _ ≤ envelopeReserve (G.induce (reserveComponentUnion G T)) k
  induction T using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Nat.zero_le _
  | @insert c T fresh ih =>
      have cover : c.supp ∪ reserveComponentUnion G T =
          reserveComponentUnion G (insert c T) := by
        ext x; exact Finset.mem_insert.symm
      have apart : Disjoint c.supp (reserveComponentUnion G T) := by
        apply Set.disjoint_left.mpr
        intro x xc xt
        exact fresh ((show G.connectedComponentMk x=c from xc) ▸ xt)
      have separate : ∀ x∈c.supp, ∀ y∈reserveComponentUnion G T, ¬G.Adj x y :=
        fun _ xc _ yt edge =>
          Set.disjoint_left.mp apart ((c.mem_supp_congr_adj edge).mp xc) yt
      let e := regionSumIso G (reserveComponentUnion G (insert c T))
        c.supp (reserveComponentUnion G T) cover apart separate
      rw [Finset.sum_insert fresh, ← envelopeReserve_iso e k]
      exact (Nat.add_le_add_left ih _).trans
        (envelopeReserve_superadditive c.toSimpleGraph
          (G.induce (reserveComponentUnion G T)) k)

/-- The original graph, with its original labels, pays for the sum of the
reserves of all its actual connected components. -/
theorem envelopeReserve_component_sum_le {X : Type*} [Finite X]
    (G : SimpleGraph X) [Fintype G.ConnectedComponent] (k : ℕ) :
    (∑ c : G.ConnectedComponent, envelopeReserve c.toSimpleGraph k) ≤
      envelopeReserve G k := by
  classical
  have result := envelopeReserve_component_finset_le G Finset.univ k
  have all : {x | G.connectedComponentMk x ∈ (Finset.univ : Finset G.ConnectedComponent)} =
      Set.univ := by ext; simp
  rw [all, envelopeReserve_iso (induceUnivIso G) k] at result
  exact result

/-- The selected region retains its exact residual-component correspondence;
no new vertex labels or replacement components are used in the sum. -/
theorem envelopeReserve_core_sum_le {X : Type*} [Finite X]
    (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) [Fintype T] (k : ℕ) :
    (∑ c : T, envelopeReserve c.val.toSimpleGraph k) ≤
      envelopeReserve (G.induce (regionCore G S T)) k := by
  classical
  let H := G.induce (regionCore G S T)
  let _ := Fintype.ofFinite H.ConnectedComponent
  calc
    (∑ c : T, envelopeReserve c.val.toSimpleGraph k) =
        ∑ c : H.ConnectedComponent, envelopeReserve c.toSimpleGraph k :=
      (Fintype.sum_equiv (coreComponentEquiv G S T) _ _
        (fun c => envelopeReserve_iso (coreComponentIso G S T c) k)).symm
    _ ≤ envelopeReserve H k := envelopeReserve_component_sum_le H k

/-- A component has all original neighbors of each of its vertices. The
equivalence is simply the original vertex label in both directions. -/
def componentNeighborEquiv {X : Type*} (G : SimpleGraph X)
    (c : G.ConnectedComponent) (x : c.supp) :
    c.toSimpleGraph.neighborSet x ≃ G.neighborSet x.val where
  toFun y := ⟨y.val.val,y.property⟩
  invFun y := ⟨⟨y.val,(c.mem_supp_congr_adj y.property).mp x.property⟩,y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem component_degree_eq {X : Type*} (G : SimpleGraph X)
    (c : G.ConnectedComponent) (x : c.supp) :
    Nat.card (c.toSimpleGraph.neighborSet x)=Nat.card (G.neighborSet x.val) :=
  Nat.card_congr (componentNeighborEquiv G c x)

private noncomputable def preconnectedComponentIso {X : Type*} (G : SimpleGraph X)
    (connected : G.Preconnected) (c : G.ConnectedComponent) : c.toSimpleGraph ≃g G := by
  have member (x : X) : x∈c.supp := by
    obtain ⟨y,hy⟩ := c.nonempty_supp
    exact (ConnectedComponent.sound (connected x y)).trans hy
  exact {
    toEquiv := {
      toFun := Subtype.val
      invFun := fun x => ⟨x,member x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    map_rel_iff' := Iff.rfl }

/-- On a nonempty preconnected graph, excluding original regular critical
components is exactly excluding regularity and criticality of that graph. -/
theorem noOriginalRegularCritical_iff_of_preconnected {X : Type*} [Nonempty X]
    (G : SimpleGraph X) (connected : G.Preconnected) (D : ℕ) :
    NoOriginalRegularCritical G D ↔
      ¬((∀ x, Nat.card (G.neighborSet x)=D) ∧ PerfectAfterEveryDeletion G) := by
  constructor
  · intro excluded both
    let c := G.connectedComponentMk (Classical.choice ‹Nonempty X›)
    let e := preconnectedComponentIso G connected c
    apply excluded c
    · intro x
      exact (component_degree_eq G c x).trans (both.1 x.val)
    · exact perfect_after_deletion_of_iso e.symm both.2
  · intro missing c regular critical
    let e := preconnectedComponentIso G connected c
    apply missing
    refine ⟨?_,perfect_after_deletion_of_iso e critical⟩
    intro x
    obtain ⟨y,rfl⟩ := e.surjective x
    exact (Nat.card_congr (e.mapNeighborSet y)).symm.trans (regular y)

/-- A component of the original graph has no hidden further component to
exclude: the condition applies precisely to the component itself. -/
theorem noOriginalRegularCritical_component_iff {X : Type*} (G : SimpleGraph X)
    (c : G.ConnectedComponent) (D : ℕ) :
    NoOriginalRegularCritical c.toSimpleGraph D ↔
      ¬((∀ x : c.supp, Nat.card (c.toSimpleGraph.neighborSet x)=D) ∧
        PerfectAfterEveryDeletion c.toSimpleGraph) := by
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  exact noOriginalRegularCritical_iff_of_preconnected c.toSimpleGraph
    c.connected_toSimpleGraph.preconnected D

theorem noOriginalRegularCritical_component_original_iff {X : Type*}
    (G : SimpleGraph X) (c : G.ConnectedComponent) (D : ℕ) :
    NoOriginalRegularCritical c.toSimpleGraph D ↔
      ¬((∀ x : c.supp, Nat.card (G.neighborSet x.val)=D) ∧
        PerfectAfterEveryDeletion c.toSimpleGraph) := by
  rw [noOriginalRegularCritical_component_iff]
  simp only [component_degree_eq]

#print axioms envelopeReserve_component_finset_le
#print axioms envelopeReserve_component_sum_le
#print axioms envelopeReserve_core_sum_le
#print axioms component_degree_eq
#print axioms noOriginalRegularCritical_component_iff
#print axioms noOriginalRegularCritical_component_original_iff
end JSP452Audit.StarHost

