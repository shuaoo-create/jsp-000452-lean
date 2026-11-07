import EvenOrientation
import Mathlib.Logic.Equiv.Sum

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- Endpoint labels on genuine undirected graph edges. -/
noncomputable def graphEnds (G : SimpleGraph X) (e : G.edgeSet) : Bool → X
  | false => e.val.out.1
  | true => e.val.out.2

theorem graphEnds_edge (G : SimpleGraph X) (e : G.edgeSet) :
    s(graphEnds G e false, graphEnds G e true) = e.val := by
  exact e.val.out_eq

theorem graphEnds_ordered_edge (G : SimpleGraph X) (e : G.edgeSet) (b : Bool) :
    s(graphEnds G e b, graphEnds G e (!b)) = e.val := by
  cases b
  · exact graphEnds_edge G e
  · exact Sym2.eq_swap.trans (graphEnds_edge G e)

/-- At each vertex the endpoint incidences of actual edge IDs are in bijection with neighbors. -/
theorem graphEnds_incidence_count (G : SimpleGraph X) (v : X) :
    Nat.card {i : G.edgeSet × Bool // graphEnds G i.1 i.2 = v} = Nat.card (G.neighborSet v) := by
  classical
  let F := {i : G.edgeSet × Bool // graphEnds G i.1 i.2 = v}
  have mem (e : G.edgeSet) (b : Bool) : graphEnds G e b ∈ e.val := by
    rw [← graphEnds_ordered_edge G e b]
    exact Sym2.mem_mk_left _ _
  let f (i : F) : G.incidenceSet v := ⟨i.val.1.val,i.val.1.property,(congrArg (fun w : X => w ∈ i.val.1.val) i.property).mp (mem i.val.1 i.val.2)⟩
  have uniq (e : G.edgeSet) : Function.Injective (graphEnds G e) := by
    have hg : G.Adj (graphEnds G e false) (graphEnds G e true) := by
      change s(graphEnds G e false,graphEnds G e true) ∈ G.edgeSet
      rw [graphEnds_edge]; exact e.property
    intro b c hb; cases b <;> cases c
    · rfl
    · exact (hg.ne hb).elim
    · exact (hg.ne hb.symm).elim
    · rfl
  have inj : Function.Injective f := by
    rintro ⟨⟨e,b⟩,hb⟩ ⟨⟨e',b'⟩,hb'⟩ h
    have he : e = e' := Subtype.ext (congrArg (fun x : G.incidenceSet v => x.val) h)
    subst e'
    exact Subtype.ext (Prod.ext rfl (uniq e (hb.trans hb'.symm)))
  have surj : Function.Surjective f := by
    intro z
    let e : G.edgeSet := ⟨z.val,z.property.1⟩
    have hz : v ∈ e.val := z.property.2
    rw [← graphEnds_edge G e, Sym2.mem_iff] at hz
    rcases hz with h | h
    · exact ⟨⟨(e,false),h.symm⟩,rfl⟩
    · exact ⟨⟨(e,true),h.symm⟩,rfl⟩
  exact (Nat.card_eq_of_bijective f ⟨inj,surj⟩).trans
    (Nat.card_congr (G.incidenceSetEquivNeighborSet v))

/-- Orientations of old-only and new-only edges, both keeping the original edge IDs. -/
structure DifferenceOrientation (F0 F1 : SimpleGraph X) (k : ℕ) where
  srcO : (F0 \ F1).edgeSet → X
  dstO : (F0 \ F1).edgeSet → X
  srcN : (F1 \ F0).edgeSet → X
  dstN : (F1 \ F0).edgeSet → X
  edgeO : ∀ e, s(srcO e, dstO e) = e.val
  edgeN : ∀ e, s(srcN e, dstN e) = e.val
  src_gap : ∀ v, Nat.card {e // srcN e = v} = Nat.card {e // srcO e = v} + k
  dst_gap : ∀ v, Nat.card {e // dstN e = v} = Nat.card {e // dstO e = v} + k

private theorem card_sum_fiber {A B : Type*} [Finite A] [Finite B] (f : A ⊕ B → X) (v : X) :
    Nat.card {e // f e = v} =
      Nat.card {a // f (.inl a) = v} + Nat.card {b // f (.inr b) = v} := by
  simpa only [Nat.card_sum] using Nat.card_congr (Equiv.subtypeSum (p := fun e => f e = v))

/-- Removing the common part subtracts the same degree at each vertex. -/
theorem difference_degree_gap [Finite X] (F0 F1 : SimpleGraph X) (a k : ℕ)
    (h0 : ∀ v, Nat.card (F0.neighborSet v) = a)
    (h1 : ∀ v, Nat.card (F1.neighborSet v) = a+2*k) (v : X) :
    Nat.card ((F1 \ F0).neighborSet v) = Nat.card ((F0 \ F1).neighborSet v) + 2*k := by
  let A := F0.neighborSet v
  let B := F1.neighborSet v
  have geA := Set.ncard_sdiff_add_ncard_of_subset (Set.inter_subset_left (s := A) (t := B))
  have geB := Set.ncard_sdiff_add_ncard_of_subset (Set.inter_subset_right (s := A) (t := B))
  have ac : A \ (A ∩ B) = A \ B := by ext; simp
  have bc : B \ (A ∩ B) = B \ A := by ext; simp
  rw [ac] at geA
  rw [bc] at geB
  change (B \ A).ncard = (A \ B).ncard + 2*k
  have aa : A.ncard = a := h0 v
  have bb : B.ncard = a+2*k := h1 v
  omega


/-- Balance the orientation of the symmetric difference, then reverse its
old-only edges. All recorded endpoints still represent their original Sym2. -/
theorem exists_difference_orientation [Finite X] (F0 F1 : SimpleGraph X) (a k : ℕ)
    (h0 : ∀ v, Nat.card (F0.neighborSet v) = a)
    (h1 : ∀ v, Nat.card (F1.neighborSet v) = a + 2*k) :
    Nonempty (DifferenceOrientation F0 F1 k) := by
  classical
  let _ := Fintype.ofFinite X
  let O := F0 \ F1
  let N := F1 \ F0
  let U := O.edgeSet ⊕ N.edgeSet
  let : Fintype O.edgeSet := Fintype.ofFinite _
  let : Fintype N.edgeSet := Fintype.ofFinite _
  let : Finite U := inferInstanceAs (Finite (O.edgeSet ⊕ N.edgeSet))
  let ends : U → Bool → X := Sum.elim (graphEnds O) (graphEnds N)
  let half (v : X) := Nat.card (O.neighborSet v) + k
  have split (p : U → Bool) (v : X) :
      Nat.card {e // ends e (p e) = v} =
        Nat.card {e // graphEnds O e (p (.inl e)) = v} +
        Nat.card {e // graphEnds N e (p (.inr e)) = v} :=
    card_sum_fiber (fun e => ends e (p e)) v
  have dg (v : X) : Nat.card {i : U × Bool // ends i.1 i.2 = v} = 2 * half v := by
    have old := orientation_incident_count (graphEnds O) (fun _ => false) v
    have new := orientation_incident_count (graphEnds N) (fun _ => false) v
    rw [graphEnds_incidence_count] at old new
    have both := orientation_incident_count ends (fun _ => false) v
    have left := split (fun _ => false) v
    have right := split (fun _ => true) v
    have gap : Nat.card (N.neighborSet v) = Nat.card (O.neighborSet v) + 2*k :=
      difference_degree_gap F0 F1 a k h0 h1 v
    simp only [Bool.not_false] at old new both
    dsimp only [half]
    omega
  obtain ⟨p,hp⟩ := exists_even_orientation ends half dg
  let srcO (e : O.edgeSet) := graphEnds O e (!(p (.inl e)))
  let dstO (e : O.edgeSet) := graphEnds O e (p (.inl e))
  let srcN (e : N.edgeSet) := graphEnds N e (p (.inr e))
  let dstN (e : N.edgeSet) := graphEnds N e (!(p (.inr e)))
  have gaps (v : X) :
      Nat.card {e // srcN e = v} = Nat.card {e // srcO e = v} + k ∧
      Nat.card {e // dstN e = v} = Nat.card {e // dstO e = v} + k := by
    have ho := orientation_incident_count (graphEnds O) (fun e => p (.inl e)) v
    rw [graphEnds_incidence_count] at ho
    obtain ⟨hleft,hright⟩ := hp v
    rw [split] at hleft
    rw [split (fun e => !(p e))] at hright
    change Nat.card {e // dstO e = v} + Nat.card {e // srcO e = v} = _ at ho
    change Nat.card {e // dstO e = v} + Nat.card {e // srcN e = v} =
      Nat.card (O.neighborSet v) + k at hleft
    change Nat.card {e // srcO e = v} + Nat.card {e // dstN e = v} =
      Nat.card (O.neighborSet v) + k at hright
    omega
  exact ⟨{
    srcO := srcO
    dstO := dstO
    srcN := srcN
    dstN := dstN
    edgeO := fun e => Sym2.eq_swap.trans (graphEnds_ordered_edge O e (p (.inl e)))
    edgeN := fun e => graphEnds_ordered_edge N e (p (.inr e))
    src_gap := fun v => (gaps v).1
    dst_gap := fun v => (gaps v).2 }⟩

#print axioms exists_difference_orientation

#print axioms graphEnds_incidence_count
#print axioms difference_degree_gap
end JSP452Audit.StarHost
