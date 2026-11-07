import CriticalComponentsOnTheActualTenDegreeSupport
namespace JSP452Audit.StarHost.TenOuterCut
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

def exteriorTargetEnds : Set X := {y|y∉K.support ∧ ∃x∈K.T,G.Adj x y}

theorem every_target_port_in_matching (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) {x y:X} (source:x∈K.T) (free:y∉K.support)
    (port:G.Adj x y) : M.Adj x y := by
  have none := (K.matching_endpoint_saturation cap M hm attained).2.2.2.2.1
  by_contra missing
  exact no_edge_when_port_zero (G \ M.spanningCoe) none source free ⟨port,missing⟩

theorem exterior_end_count (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) : K.exteriorTargetEnds.ncard=K.targetPorts := by
  let A := {p:↥K.T × ↥K.supportᶜ|G.Adj p.1.val p.2.val}
  let endOf (p:↥A) : ↥K.exteriorTargetEnds := ⟨p.val.2.val,p.val.2.property,p.val.1.val,p.val.1.property,p.property⟩
  have inj : Function.Injective endOf := by
    intro p q eq
    have same : p.val.2.val=q.val.2.val := congrArg (fun z:↥K.exteriorTargetEnds => z.val) eq
    have e := K.every_target_port_in_matching cap M hm attained p.val.1.property p.val.2.property p.property
    have f := K.every_target_port_in_matching cap M hm attained q.val.1.property q.val.2.property q.property
    rw [same] at e
    have left := hm.eq_of_adj_left e.symm f.symm
    exact Subtype.ext (Prod.ext (Subtype.ext left) (Subtype.ext same))
  have surj : Function.Surjective endOf := by
    rintro ⟨y,out,x,mem,edge⟩
    exact ⟨⟨(⟨x,mem⟩,⟨y,out⟩),edge⟩,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective endOf ⟨inj,surj⟩)).symm

theorem exterior_end_has_no_exterior_matching_edge (cap:∀x,Nat.card (G.neighborSet x)≤10)
    (M:G.Subgraph) (hm:M.IsMatching) (attained:(exposedFull G M 10).ncard=K.score+2) :
    ∀y∈K.exteriorTargetEnds,∀z∉K.support,¬M.Adj y z := by
  rintro y ⟨out,x,mem,e⟩ z outside f
  have port := K.every_target_port_in_matching cap M hm attained mem out e
  have same := hm.eq_of_adj_left f port.symm
  exact outside (same ▸ (show x∈K.support from Or.inl (Or.inr mem)))

#print axioms every_target_port_in_matching
#print axioms exterior_end_count
#print axioms exterior_end_has_no_exterior_matching_edge
end JSP452Audit.StarHost.TenOuterCut
