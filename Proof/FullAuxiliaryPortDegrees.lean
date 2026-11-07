import PairedFiveVertexExtension
namespace JSP452Audit.StarHost
open SimpleGraph

theorem block_neighbor_count (p:Fin 5) :
    ({q:Fin 5|fiveBlockAdj p q}:Set (Fin 5)).ncard+({j:Fin 2|portEmbedding j=p}:Set (Fin 2)).ncard=4 := by
  let a (p:Fin 5) := Finset.univ.filter (fun q:Fin 5 => p≠q ∧ ¬(p.val<2 ∧ q.val<2))
  let b (p:Fin 5) := Finset.univ.filter (fun j:Fin 2 => portEmbedding j=p)
  have finite : ∀q:Fin 5,(a q).card+(b q).card=4 := by decide +kernel
  have left : (↑(a p):Set (Fin 5))={q:Fin 5|fiveBlockAdj p q} := by ext;simp [a,fiveBlockAdj]
  have right : (↑(b p):Set (Fin 2))={j:Fin 2|portEmbedding j=p} := by ext;simp [b]
  rw [←left,←right,Set.ncard_coe_finset,Set.ncard_coe_finset]
  exact finite p

theorem new_vertex_paired_extension_degree {X I:Type*} [Finite X] [Finite I] (Q:SimpleGraph X)
    (t:I×Fin 2→X) (i:I) (p:Fin 5) :
    Nat.card ((pairedExtension Q t).neighborSet (.inr (i,p)))=4 := by
  let V := X⊕(I×Fin 5)
  let L : Set (Fin 5) := {q|fiveBlockAdj p q}
  let J : Set (Fin 2) := {j|portEmbedding j=p}
  let f (q:Fin 5) : V := .inr (i,q)
  let g (j:Fin 2) : V := .inl (t (i,j))
  have neighbors : (pairedExtension Q t).neighborSet (.inr (i,p))=f '' L∪g '' J := by
    ext v
    cases v with
    | inl x =>
      constructor
      · rintro ⟨j,eq,tx⟩;exact Or.inr ⟨j,eq,congrArg Sum.inl tx⟩
      · rintro (⟨q,_,eq⟩|⟨j,hj,eq⟩)
        · cases eq
        · exact ⟨j,hj,Sum.inl.inj eq⟩
    | inr z =>
      rcases z with ⟨k,q⟩
      constructor
      · rintro ⟨eq,e⟩
        exact Or.inl ⟨q,e,congrArg Sum.inr (congrArg (fun a => (a,q)) eq)⟩
      · rintro (⟨w,hw,eq⟩|⟨j,_,eq⟩)
        · have same : (i,w)=(k,q) := Sum.inr.inj eq
          have ik : i=k := congrArg Prod.fst same
          have wq : w=q := congrArg Prod.snd same
          exact ⟨ik,wq ▸ hw⟩
        · cases eq
  have dis : Disjoint (f '' L) (g '' J) := Set.disjoint_left.mpr (by
    rintro _ ⟨q,_,rfl⟩ ⟨j,_,eq⟩;cases eq)
  have fi : Function.Injective f := fun _ _ eq => congrArg Prod.snd (Sum.inr.inj eq)
  have gi : Set.InjOn g J := fun j hj k hk _ => portEmbedding.injective (hj.trans hk.symm)
  rw [neighbors,Nat.card_coe_set_eq,Set.ncard_union_eq dis,Set.ncard_image_of_injective _ fi,gi.ncard_image]
  exact block_neighbor_count p

#print axioms block_neighbor_count
#print axioms new_vertex_paired_extension_degree
end JSP452Audit.StarHost
