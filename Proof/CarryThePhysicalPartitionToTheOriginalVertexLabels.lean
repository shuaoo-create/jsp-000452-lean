import PhysicalRootCoreAndExteriorWithADegreeDeficit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def inducedImageIso {X Y:Type u} {G:SimpleGraph X} {H:SimpleGraph Y}
    (e:G≃g H) (A:Set X) : G.induce A ≃g H.induce (e '' A) :=
  e.induce ⟨Set.mapsTo_image _ _,e.injective.injOn,Set.surjOn_image _ _⟩

theorem original_degrees_image_iso {X Y:Type u} [Finite X] [Finite Y] {G:SimpleGraph X} {H:SimpleGraph Y}
    (e:G≃g H) (A:Set X) : originalDegreeSum H (e '' A)=originalDegreeSum G A := by
  classical
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite ↥(e '' A)
  have expand {Z:Type u} [Finite Z] (K:SimpleGraph Z) (U:Set Z) [Fintype U] :
      originalDegreeSum K U=∑x:↥U,(K.neighborSet x.val).ncard :=
    Finset.sum_subtype U.toFinite.toFinset (fun _ => U.toFinite.mem_toFinset) _
  rw [expand,expand]
  let f := inducedImageIso e A
  symm
  apply Fintype.sum_equiv f.toEquiv
  intro x
  exact Nat.card_congr (e.mapNeighborSet x.val)

namespace TenBlockPartition
variable {X Y:Type u} [Finite X] [Finite Y] {G:SimpleGraph X} {H:SimpleGraph Y}
noncomputable def transport (P:TenBlockPartition G) (e:G≃g H) : TenBlockPartition H where
  roots := e '' P.roots
  core := e '' P.core
  rest := e '' P.rest
  eta := P.eta
  epsilon := P.epsilon
  rootsCore := Set.disjoint_image_of_injective e.injective P.rootsCore
  rootsRest := Set.disjoint_image_of_injective e.injective P.rootsRest
  coreRest := Set.disjoint_image_of_injective e.injective P.coreRest
  cover := by rw [←Set.image_union,←Set.image_union,P.cover,Set.image_univ,e.surjective.range_eq]
  apart := by rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ edge;exact P.apart x hx y hy (e.map_rel_iff.mp edge)
  rank := by rw [←rank_eq_of_graph_iso e,←rank_eq_of_graph_iso (inducedImageIso e P.core),
      ←rank_eq_of_graph_iso (inducedImageIso e P.rest),Set.ncard_image_of_injective _ e.injective];exact P.rank
  order := by rw [←rank_eq_of_graph_iso (inducedImageIso e P.core),Set.ncard_image_of_injective _ e.injective,
      Set.ncard_image_of_injective _ e.injective];exact P.order
  degrees := by rw [original_degrees_image_iso,Set.ncard_image_of_injective _ e.injective];exact P.degrees
  critical := odd_critical_family_of_iso (inducedImageIso e P.core) P.critical
end TenBlockPartition
#print axioms inducedImageIso
#print axioms original_degrees_image_iso
#print axioms TenBlockPartition.transport
end JSP452Audit.StarHost
