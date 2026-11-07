import GeneralPairedPortExtension
namespace JSP452Audit.StarHost.PairedLayers
open SimpleGraph
variable (k:ℕ)

theorem block_neighbor_count (p:Fin (2*(k+1)+1)) :
    ({q:Fin (2*(k+1)+1)|blockAdj k p q}:Set (Fin (2*(k+1)+1))).ncard+({j:Fin 2|(portEmbedding k) j=p}:Set (Fin 2)).ncard=2*(k+1) := by
  classical
  let ports := Set.range (portEmbedding k)
  have size : ports.ncard=2 := by
    rw [Set.ncard_range_of_injective (portEmbedding k).injective,Nat.card_fin]
  have mem (q:Fin (2*(k+1)+1)) : q∈ports ↔ q.val<2 := by
    constructor
    · rintro ⟨j,rfl⟩;exact j.isLt
    · intro h;exact ⟨⟨q.val,h⟩,Fin.ext rfl⟩
  by_cases hp:p.val<2
  · obtain ⟨j,eq⟩ := (mem p).mpr hp
    have one : {a:Fin 2|(portEmbedding k) a=p}=({j}:Set _) := by
      ext a;simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff,←eq,EmbeddingLike.apply_eq_iff_eq]
    have internal : {q|blockAdj k p q}=portsᶜ := by
      ext q
      change (p≠q ∧ ¬(p.val<2 ∧ q.val<2)) ↔ q∉ports
      rw [mem];constructor
      · exact fun e h => e.2 ⟨hp,h⟩
      · intro h;exact ⟨fun eq => h (eq ▸ hp),fun b => h b.2⟩
    rw [internal,one,Set.ncard_singleton,Set.ncard_compl,size,Nat.card_fin]
    omega
  · have zero : {a:Fin 2|(portEmbedding k) a=p}=∅ :=
      Set.eq_empty_of_forall_notMem (fun a eq => hp ((mem p).mp ⟨a,eq⟩))
    have internal : {q|blockAdj k p q}=({p}:Set _)ᶜ := by
      ext q;simp [blockAdj,hp,ne_comm]
    rw [internal,zero,Set.ncard_empty,Set.ncard_compl,Set.ncard_singleton,Nat.card_fin]
    omega

theorem new_vertex_paired_extension_degree {X I:Type*} [Finite X] [Finite I] (Q:SimpleGraph X)
    (t:I×Fin 2→X) (i:I) (p:Fin (2*(k+1)+1)) :
    Nat.card ((pairedExtension k Q t).neighborSet (.inr (i,p)))=2*(k+1) := by
  let V := X⊕(I×Fin (2*(k+1)+1))
  let L : Set (Fin (2*(k+1)+1)) := {q|blockAdj k p q}
  let J : Set (Fin 2) := {j|(portEmbedding k) j=p}
  let f (q:Fin (2*(k+1)+1)) : V := .inr (i,q)
  let g (j:Fin 2) : V := .inl (t (i,j))
  have neighbors : (pairedExtension k Q t).neighborSet (.inr (i,p))=f '' L∪g '' J := by
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
  have gi : Set.InjOn g J := fun j hj j' hk _ => (portEmbedding k).injective (hj.trans hk.symm)
  rw [neighbors,Nat.card_coe_set_eq,Set.ncard_union_eq dis,Set.ncard_image_of_injective _ fi,gi.ncard_image]
  exact block_neighbor_count k p

#print axioms block_neighbor_count
#print axioms new_vertex_paired_extension_degree
end JSP452Audit.StarHost.PairedLayers
