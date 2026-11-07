import SignedExposureFromLayerOwners
namespace JSP452Audit.StarHost.PairedLayers

open SimpleGraph
variable (k:ℕ)
def portEmbedding : Fin 2 ↪ Fin (2*(k+1)+1) := Fin.castLEEmb (by omega)
def blockAdj (p q:Fin (2*(k+1)+1)) : Prop := p≠q ∧ ¬(p.val<2 ∧ q.val<2)
def hook {X I:Type*} (t:I×Fin 2→X) (x:X) (z:I×Fin (2*(k+1)+1)) : Prop :=
  ∃j:Fin 2,(portEmbedding k) j=z.2 ∧ t (z.1,j)=x

def pairedExtension {X I:Type*} (Q:SimpleGraph X) (t:I×Fin 2→X) : SimpleGraph (X⊕(I×Fin (2*(k+1)+1))) where
  Adj
    | .inl x,.inl y => Q.Adj x y
    | .inl x,.inr z => hook k t x z
    | .inr z,.inl x => hook k t x z
    | .inr a,.inr b => a.1=b.1 ∧ blockAdj k a.2 b.2
  symm := ⟨by
    rintro (x|x) (y|y) e
    · exact e.symm
    · exact e
    · exact e
    · exact ⟨e.1.symm,e.2.1.symm,fun h => e.2.2 h.symm⟩⟩
  loopless := ⟨by rintro (v|v) h;exact Q.loopless.irrefl v h;exact h.2.1 rfl⟩

def portNode {I:Type*} (i:I) (j:Fin 2) : I×Fin (2*(k+1)+1) := (i,(portEmbedding k) j)
def blockSet {X I:Type*} (i:I) : Set (X⊕(I×Fin (2*(k+1)+1))) := Set.range (fun p:Fin (2*(k+1)+1) => Sum.inr (i,p))

theorem old_neighbor_equiv {X I:Type*} (Q:SimpleGraph X) (t:I×Fin 2→X) (v:X) :
    Nonempty (((pairedExtension k Q t).neighborSet (Sum.inl v)) ≃ (Q.neighborSet v ⊕ {a:I×Fin 2 // t a=v})) := by
  classical
  let send (z:(pairedExtension k Q t).neighborSet (Sum.inl v)) : Q.neighborSet v ⊕ {a:I×Fin 2 // t a=v} :=
    match z with
    | ⟨.inl x,e⟩ => .inl ⟨x,e⟩
    | ⟨.inr (i,p),h⟩ =>
      let j := (show hook k t v (i,p) from h).choose
      .inr ⟨(i,j),(show hook k t v (i,p) from h).choose_spec.2⟩
  let back : Q.neighborSet v ⊕ {a:I×Fin 2 // t a=v} → (pairedExtension k Q t).neighborSet (Sum.inl v) := fun z =>
    match z with
    | .inl x => ⟨.inl x.val,x.property⟩
    | .inr a => ⟨.inr (portNode k a.val.1 a.val.2),a.val.2,rfl,a.property⟩
  refine ⟨{toFun := send,invFun := back,left_inv := ?_,right_inv := ?_}⟩
  · rintro ⟨x|⟨i,p⟩,edge⟩
    · rfl
    · apply Subtype.ext
      exact congrArg (fun z => Sum.inr (i,z)) (show hook k t v (i,p) from edge).choose_spec.1
  · rintro (x|⟨⟨i,j⟩,h⟩)
    · rfl
    · apply congrArg Sum.inr
      apply Subtype.ext
      have e : hook k t v (i,(portEmbedding k) j) := ⟨j,rfl,h⟩
      exact congrArg (Prod.mk i) ((portEmbedding k).injective e.choose_spec.1)

theorem original_paired_extension_degree {X I:Type*} [Finite X] [Finite I] (Q:SimpleGraph X)
    (t:I×Fin 2→X) (v:X) :
    Nat.card ((pairedExtension k Q t).neighborSet (.inl v))=Nat.card (Q.neighborSet v)+Nat.card {a:I×Fin 2 // t a=v} := by
  obtain ⟨e⟩ := old_neighbor_equiv k Q t v
  exact (Nat.card_congr e).trans Nat.card_sum

#print axioms old_neighbor_equiv
#print axioms original_paired_extension_degree
end JSP452Audit.StarHost.PairedLayers
