import TwoPortCutInAnActualPalette
namespace JSP452Audit.StarHost
open SimpleGraph

theorem palette_labels_at_original_vertex {X I:Type*} [Finite X] [Finite I] (t:I×Fin 2→X)
    (R:SimpleGraph (X⊕(I×Fin 5))) (A:Set (I×Fin 2))
    (usePort:∀a∈A,R.Adj (.inr (portNode a.1 a.2)) (.inl (t a))) (v:X) :
    ((R.comap Sum.inl).neighborSet v).ncard+({a:I×Fin 2|a∈A ∧ t a=v}:Set (I×Fin 2)).ncard≤
      (R.neighborSet (.inl v)).ncard := by
  let F := {a:I×Fin 2|a∈A ∧ t a=v}
  let send : ((R.comap Sum.inl).neighborSet v) ⊕ ↥F → R.neighborSet (.inl v) := fun z =>
    match z with
    | .inl x => ⟨.inl x.val,x.property⟩
    | .inr a => ⟨.inr (portNode a.val.1 a.val.2),a.property.2 ▸ (usePort a.val a.property.1).symm⟩
  have inj : Function.Injective send := by
    rintro (x|a) (y|b) eq
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj (congrArg Subtype.val eq)))
    · have eqv := congrArg Subtype.val eq;cases eqv
    · have eqv := congrArg Subtype.val eq;cases eqv
    · apply congrArg Sum.inr
      apply Subtype.ext
      have pair : portNode a.val.1 a.val.2=portNode b.val.1 b.val.2 := Sum.inr.inj (congrArg Subtype.val eq)
      have fst : a.val.1=b.val.1 := congrArg (fun z:I×Fin 5 => z.1) pair
      have snd : portEmbedding a.val.2=portEmbedding b.val.2 := congrArg (fun z:I×Fin 5 => z.2) pair
      exact Prod.ext fst (portEmbedding.injective snd)
  have bound := Nat.card_le_card_of_injective send inj
  rwa [Nat.card_sum] at bound

theorem paired_port_split {X I:Type*} [Finite X] [Finite I] (Q:SimpleGraph X) (t:I×Fin 2→X)
    (cap:∀v,Nat.card (Q.neighborSet v)+Nat.card {a:I×Fin 2 // t a=v}≤4) :
    ∃R:SimpleGraph X,R≤Q ∧ ∃K:Set I,
      (∀v,(R.neighborSet v).ncard+({a:I×Fin 2|a.1∈K ∧ t a=v}:Set _).ncard≤2) ∧
      (∀v,((Q \ R).neighborSet v).ncard+({a:I×Fin 2|a.1∉K ∧ t a=v}:Set _).ncard≤2) := by
  let H := pairedExtension Q t
  have bound (v:X⊕(I×Fin 5)) : Nat.card (H.neighborSet v)≤2*(1+1) := by
    cases v with
    | inl x => exact (original_paired_extension_degree Q t x).trans_le (cap x)
    | inr z => exact (new_vertex_paired_extension_degree Q t z.1 z.2).le
  obtain ⟨A,sub,split⟩ := even_even_degree_split H 1 1 bound
  let R := A.comap Sum.inl
  let K := {i:I|(0:Fin 2)∈activePorts t A i}
  have colors (i:I) (j:Fin 2) : j∈activePorts t A i ↔ i∈K := by
    fin_cases j
    · rfl
    · exact (two_ports_same_color Q t A sub split i).symm
  have keep (a:I×Fin 2) (on:a.1∈K) : A.Adj (.inr (portNode a.1 a.2)) (.inl (t a)) := (colors a.1 a.2).mpr on
  have flip (a:I×Fin 2) (off:a.1∉K) : (H \ A).Adj (.inr (portNode a.1 a.2)) (.inl (t a)) :=
    ⟨⟨a.2,rfl,rfl⟩,fun red => off ((colors a.1 a.2).mp red)⟩
  have blueEq : (H \ A).comap Sum.inl=Q \ R := rfl
  refine ⟨R,(fun _ _ edge => sub edge),K,?_,?_⟩
  · intro v
    have lower := palette_labels_at_original_vertex t A {a|a.1∈K} keep v
    exact lower.trans (split (.inl v)).1
  · intro v
    have lower := palette_labels_at_original_vertex t (H \ A) {a|a.1∉K} flip v
    rw [blueEq] at lower
    exact lower.trans (split (.inl v)).2

#print axioms palette_labels_at_original_vertex
#print axioms paired_port_split
end JSP452Audit.StarHost
