import ChooseTheActualPortEndpointAndTheInternalMatchingHoleInEveryCore
namespace JSP452Audit.StarHost
open SimpleGraph
universe u v
variable {X:Type u} {I:Type v}

def originalPortEdges (G:SimpleGraph X) (p z:I→X) (links:∀i,G.Adj (p i) (z i)) : SimpleGraph X where
  Adj x y := (∃i,p i=x ∧ z i=y) ∨ (∃i,p i=y ∧ z i=x)
  symm := ⟨fun _ _ e => e.symm⟩
  loopless := ⟨by
    intro x e;rcases e with ⟨i,pair⟩|⟨i,pair⟩ <;> exact (links i).ne (pair.1.trans pair.2.symm)⟩

theorem original_ports_are_edges (G:SimpleGraph X) (p z:I→X) (links:∀i,G.Adj (p i) (z i)) : originalPortEdges G p z links≤G := by
  rintro x y (⟨i,rfl,rfl⟩|⟨i,rfl,rfl⟩);exact links i;exact (links i).symm

theorem original_port_valences [Finite X] (G:SimpleGraph X) (S:Set X) (p z:I→X) (links:∀i,G.Adj (p i) (z i))
    (roots:∀i,p i∈S) (outside:∀i,z i∉S) (inj:Function.Injective z) :
    let H := originalPortEdges G p z links
    (∀x∈S,Nat.card (H.neighborSet x)=Nat.card {i // p i=x}) ∧
      (∀i,Nat.card (H.neighborSet (z i))=1) ∧
      (∀x,x∉S → x∉Set.range z → Nat.card (H.neighborSet x)=0) := by
  classical
  intro H
  constructor
  · intro x root
    let send (i:{i // p i=x}) : H.neighborSet x := ⟨z i.val,Or.inl ⟨i.val,i.property,rfl⟩⟩
    have inject : Function.Injective send := fun _ _ e => Subtype.ext (inj (congrArg (fun a:H.neighborSet x => a.val) e))
    have surj : Function.Surjective send := by
      rintro ⟨y,adj⟩
      rcases adj with ⟨i,px,rfl⟩|⟨i,_,zx⟩
      · exact ⟨⟨i,px⟩,rfl⟩
      · exact (outside i (zx.symm ▸ root)).elim
    exact (Nat.card_congr (Equiv.ofBijective send ⟨inject,surj⟩)).symm
  constructor
  · intro i
    have setEq : H.neighborSet (z i)={p i} := by
      ext x
      constructor
      · rintro (⟨j,eq,_⟩|⟨j,rfl,e⟩)
        · exact (outside i (eq ▸ roots j)).elim
        · exact congrArg p (inj e)
      · rintro rfl;exact Or.inr ⟨i,rfl,rfl⟩
    rw [Nat.card_coe_set_eq,setEq,Set.ncard_singleton]
  · intro x away unused
    have eq : H.neighborSet x=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y (⟨i,eq,_⟩|⟨i,_,atX⟩)
      · exact away (eq ▸ roots i)
      · exact unused ⟨i,atX⟩
    rw [Nat.card_coe_set_eq,eq,Set.ncard_empty]

#print axioms original_ports_are_edges
#print axioms original_port_valences
end JSP452Audit.StarHost
