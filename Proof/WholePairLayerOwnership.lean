import RestrictTwoDegreeLayers
namespace JSP452Audit.StarHost.PairedLayers
open SimpleGraph
variable (k:ℕ)

theorem palette_labels_at_original_vertex {X I:Type*} [Finite X] [Finite I] (t:I×Fin 2→X)
    (R:SimpleGraph (X⊕(I×Fin (2*(k+1)+1)))) (A:Set (I×Fin 2))
    (usePort:∀a∈A,R.Adj (.inr (portNode k a.1 a.2)) (.inl (t a))) (v:X) :
    ((R.comap Sum.inl).neighborSet v).ncard+({a:I×Fin 2|a∈A ∧ t a=v}:Set (I×Fin 2)).ncard≤
      (R.neighborSet (.inl v)).ncard := by
  let F := {a:I×Fin 2|a∈A ∧ t a=v}
  let send : ((R.comap Sum.inl).neighborSet v) ⊕ ↥F → R.neighborSet (.inl v) := fun z =>
    match z with
    | .inl x => ⟨.inl x.val,x.property⟩
    | .inr a => ⟨.inr (portNode k a.val.1 a.val.2),a.property.2 ▸ (usePort a.val a.property.1).symm⟩
  have inj : Function.Injective send := by
    rintro (x|a) (y|b) eq
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj (congrArg Subtype.val eq)))
    · have eqv := congrArg Subtype.val eq;cases eqv
    · have eqv := congrArg Subtype.val eq;cases eqv
    · apply congrArg Sum.inr
      apply Subtype.ext
      have pair : portNode k a.val.1 a.val.2=portNode k b.val.1 b.val.2 := Sum.inr.inj (congrArg Subtype.val eq)
      have fst : a.val.1=b.val.1 := congrArg (fun z:I×Fin (2*(k+1)+1) => z.1) pair
      have snd : (portEmbedding k) a.val.2=(portEmbedding k) b.val.2 := congrArg (fun z:I×Fin (2*(k+1)+1) => z.2) pair
      exact Prod.ext fst ((portEmbedding k).injective snd)
  have bound := Nat.card_le_card_of_injective send inj
  rwa [Nat.card_sum] at bound

theorem paired_port_layers {X I:Type*} [Finite X] [Finite I] (Q:SimpleGraph X) (t:I×Fin 2→X)
    (cap:∀v,Nat.card (Q.neighborSet v)+Nat.card {a:I×Fin 2 // t a=v}≤2*(k+1)) :
    ∃V:TwoDegreeLayers Q (k+1),∃owner:I→Fin (k+1),∀j v,
      ((V.part j).neighborSet v).ncard+({a:I×Fin 2|owner a.1=j ∧ t a=v}:Set _).ncard≤2 := by
  classical
  let H := pairedExtension k Q t
  have bound (v:X⊕(I×Fin (2*(k+1)+1))) : Nat.card (H.neighborSet v)≤2*(k+1) := by
    cases v with
    | inl x => exact (original_paired_extension_degree k Q t x).trans_le (cap x)
    | inr z => exact (new_vertex_paired_extension_degree k Q t z.1 z.2).le
  obtain ⟨V⟩ := actual_even_cap_layers (k+1) H bound
  have atZero (i:I) : ∃j:Fin (k+1),(0:Fin 2)∈activePorts k t (V.part j) i :=
    V.cover (.inr (portNode k i 0)) (.inl (t (i,0))) ⟨0,rfl,rfl⟩
  choose owner owned using atZero
  let emb : X↪(X⊕(I×Fin (2*(k+1)+1))) := ⟨Sum.inl,Sum.inl_injective⟩
  let U : TwoDegreeLayers Q (k+1) := V.restrict emb
  refine ⟨U,owner,?_⟩
  intro j v
  have attached (a:I×Fin 2) (assigned:owner a.1=j) :
      (V.part j).Adj (.inr (portNode k a.1 a.2)) (.inl (t a)) := by
    subst j
    rcases a with ⟨i,h⟩
    fin_cases h
    · exact owned i
    · exact (two_ports_same_layer k Q t V (owner i) i).mp (owned i)
  exact (palette_labels_at_original_vertex k t (V.part j) {a|owner a.1=j} attached v).trans (V.cap j (.inl v))

#print axioms palette_labels_at_original_vertex
#print axioms paired_port_layers
end JSP452Audit.StarHost.PairedLayers
