import CoreReach
import CoreBoundary
namespace JSP452Audit.Padded
open SimpleGraph
variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj] {S T : Set V}

noncomputable def Spec.coreRep (C : P.CoreComponent S T) : P.CanonVertex S T :=
  P.coreAnchor C.nonempty_supp.choose

theorem Spec.onCore_rep (C : P.CoreComponent S T) : P.onCore C (P.coreRep C).val :=
  ⟨C.nonempty_supp.choose.property,C.nonempty_supp.choose_spec⟩

noncomputable def Spec.coreCC (C : P.CoreComponent S T) : (P.canonGraph S T).ConnectedComponent :=
  (P.canonGraph S T).connectedComponentMk (P.coreRep C)

theorem Spec.has_core_cc {C : P.CoreComponent S T} {z : P.CanonVertex S T} (hz : P.onCore C z.val) :
    (P.canonGraph S T).connectedComponentMk z = P.coreCC C :=
  ConnectedComponent.sound (P.onCore_reachable C hz (P.onCore_rep C))

theorem Spec.tight_core_mem {C : P.CoreComponent S T} (tight : P.coreTight C)
    (z : P.CanonVertex S T) : z ∈ (P.coreCC C).supp ↔ P.onCore C z.val := by
  constructor
  · intro hz
    have walk := (P.coreCC C).reachable_of_mem_supp (u := P.coreRep C) (by rfl) hz
    rw [reachable_iff_reflTransGen] at walk
    clear hz
    induction walk with
    | refl => exact P.onCore_rep C
    | tail _ edge ih => exact P.coreTight_closed tight ih edge
  · exact P.has_core_cc

def Spec.tightFiberEquiv {C : P.CoreComponent S T} (dis : Disjoint S T) (tight : P.coreTight C) :
    (P.coreCC C).supp ≃ {z : P.Vertex // P.onCore C z} where
  toFun z := ⟨z.val.val,(P.tight_core_mem tight z.val).mp z.property⟩
  invFun z := ⟨P.canonicalPoint z.val (P.onCore_kept dis z.property),(P.tight_core_mem tight _).mpr z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Spec.tightOdd (S T : Set V) : Set (P.CoreComponent S T) :=
  {C | P.coreTight C ∧ Odd (Nat.card {z : P.Vertex // P.onCore C z})}

#print axioms Spec.tight_core_mem
#print axioms Spec.tightFiberEquiv
end JSP452Audit.Padded
