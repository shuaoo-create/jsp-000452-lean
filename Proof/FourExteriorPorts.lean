import FourRegularEnvelopeProjection
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Each exterior label that is needed to retain a full neighbourhood can
be charged to one actual incidence, even if many stars see the same label. -/
theorem exterior_port_count (G : SimpleGraph X) (T B : Set X) :
    ({w | w∈B ∧ ∃v∈T,G.Adj v w}:Set X).ncard≤crossCount G T B := by
  let P := {w | w∈B ∧ ∃v∈T,G.Adj v w}
  let R := {p : ↥T × ↥B // G.Adj p.1.val p.2.val}
  let f (w:↥P) : R := ⟨(⟨w.property.2.choose,w.property.2.choose_spec.1⟩,⟨w.val,w.property.1⟩),
    w.property.2.choose_spec.2⟩
  have inj : Function.Injective f := fun a b eq => Subtype.ext (congrArg (fun z:R => z.val.2.val) eq)
  exact Nat.card_le_card_of_injective f inj

/-- Adjoin precisely the exterior labels seen by the target vertices.
All their original neighbours survive. The regular envelope projection
therefore gives a genuine dominating set in the original graph. -/
theorem four_dominates_via_actual_ports (G : SimpleGraph X) (Y B T : Set X)
    (apart : Disjoint Y B) (cover : Y∪B=Set.univ) (sub : T⊆Y)
    (full : ∀v∈T,Nat.card (G.neighborSet v)=4) (cap : ∀v,Nat.card (G.neighborSet v)≤4) :
    ∃S:Set X,(∀v∈T,v∈S ∨ ∃w∈S,G.Adj v w) ∧ 13*S.ncard≤5*(Y.ncard+crossCount G T B) := by
  classical
  let P := {w | w∈B ∧ ∃v∈T,G.Adj v w}
  let W := Y∪P
  have countP : P.ncard≤crossCount G T B := exterior_port_count G T B
  have pB : P⊆B := fun _ h => h.1
  have dis : Disjoint Y P := apart.mono_right pB
  have capW (w:↥W) : Nat.card ((G.induce W).neighborSet w)≤4 :=
    (induced_neighbor_count_le G W w).trans (cap _)
  have here (v:X) (hv:v∈T) (w:X) (adj:G.Adj v w) : w∈W := by
    rcases (show w∈Y∪B from cover.symm ▸ Set.mem_univ w) with y|b
    · exact Or.inl y
    · exact Or.inr ⟨b,v,hv,adj⟩
  have degree (v:X) (hv:v∈T) : Nat.card ((G.induce W).neighborSet ⟨v,Or.inl (sub hv)⟩)=4 := by
    let y : W := ⟨v,Or.inl (sub hv)⟩
    let f (w:G.neighborSet v) : (G.induce W).neighborSet y := ⟨⟨w.val,here v hv _ w.property⟩,w.property⟩
    have up := Nat.card_le_card_of_injective f (fun a b eq => Subtype.ext (congrArg
      (fun z:(G.induce W).neighborSet y => z.val.val) eq))
    rw [full v hv] at up
    exact le_antisymm (capW y) up
  obtain ⟨S,hit,cost⟩ := four_partial_domination (G.induce W) capW
  let chosen := Subtype.val '' S
  have size : chosen.ncard=S.ncard := Set.ncard_image_of_injective S Subtype.val_injective
  refine ⟨chosen,?_,?_⟩
  · intro v hv
    rcases hit ⟨v,Or.inl (sub hv)⟩ (degree v hv) with sel|⟨w,sel,adj⟩
    · exact Or.inl ⟨_,sel,rfl⟩
    · exact Or.inr ⟨w.val,⟨w,sel,rfl⟩,adj⟩
  · rw [size]
    rw [Nat.card_coe_set_eq] at cost
    change 13*S.ncard≤5*(Y∪P).ncard at cost
    rw [Set.ncard_union_eq dis] at cost
    omega

#print axioms exterior_port_count
#print axioms four_dominates_via_actual_ports
end JSP452Audit.StarHost
