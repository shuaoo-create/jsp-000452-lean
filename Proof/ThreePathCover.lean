import ZeroCutMatching
import ThreePathRootSelection
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Realize a matching covering an even clique and two disjoint genuine
edges outside it. Empty clique permitted. -/
private theorem cover_even_clique_and_endpoints (H : SimpleGraph X) (C : Set X) (cl : H.IsClique C)
    (even : Even C.ncard) (a b i j : X) (ai : H.Adj a i) (bj : H.Adj b j)
    (outside : ∀x,x∈({a,i,b,j} : Set X) → x∉C)
    (apart : Disjoint ({a,i} : Set X) ({b,j} : Set X)) :
    ∃M : H.Subgraph,M.IsMatching ∧ C⊆M.verts ∧ a∈M.verts ∧ b∈M.verts ∧ i∈M.verts ∧ j∈M.verts := by
  classical
  let e : C ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨P,mP,supp⟩ := JSP452Audit.Padded.existsMatchingOnEvenClique H e
    (fun {u v} ne => cl u.property v.property (fun eq => ne (Subtype.ext eq)))
    (by rwa [Nat.card_coe_set_eq])
  have pc : P.verts=C := supp.trans (by ext x; exact ⟨fun ⟨y,eq⟩ => eq ▸ y.property,
    fun hx => ⟨⟨x,hx⟩,rfl⟩⟩)
  let L := H.subgraphOfAdj ai
  let R := H.subgraphOfAdj bj
  have l : L.verts={a,i} := rfl
  have r : R.verts={b,j} := rfl
  have mlr := JSP452Audit.Padded.matching_sup_of_disjoint_verts H (Subgraph.IsMatching.subgraphOfAdj ai)
    (Subgraph.IsMatching.subgraphOfAdj bj) apart
  have sep : Disjoint P.verts (L⊔R).verts := by
    rw [pc,Subgraph.verts_sup,l,r]
    apply Set.disjoint_left.mpr
    rintro x cx ((eq|eq)|(eq|eq))
    · exact outside x (Or.inl eq) cx
    · exact outside x (Or.inr (Or.inl (Set.mem_singleton_iff.mp eq))) cx
    · exact outside x (Or.inr (Or.inr (Or.inl eq))) cx
    · exact outside x (Or.inr (Or.inr (Or.inr eq))) cx
  refine ⟨P⊔(L⊔R),JSP452Audit.Padded.matching_sup_of_disjoint_verts H mP mlr sep,?_,?_,?_,?_,?_⟩
  · intro x hx; exact Or.inl (pc ▸ hx)
  · exact Or.inr (Or.inl (show a∈L.verts from Or.inl rfl))
  · exact Or.inr (Or.inr (show b∈R.verts from Or.inl rfl))


  · exact Or.inr (Or.inl (show i∈L.verts from Or.inr rfl))
  · exact Or.inr (Or.inr (show j∈R.verts from Or.inr rfl))

/-- The vertex types here live in the graph after the paid deletion. The
D+1 incidence bound allows its full roots to be matched to the two leaves. -/
theorem path_clique_matching_remainder (H : SimpleGraph X) (D : ℕ) (large : 6≤D)
    (R K : Set X) (a b : X) (ab : a≠b) (ind : H.IsIndepSet R)
    (dis : Disjoint R K) (ar : a∉R) (br : b∉R) (ak : a∉K) (bk : b∉K)
    (cover : ∀v,v∈R ∨ v=a ∨ v=b ∨ v∈K)
    (cl : H.IsClique K) (even : Even K.ncard) (order : K.ncard=D-2)
    (cap : ∀v,Nat.card (H.neighborSet v)≤D-1)
    (roots : crossCount H R K≤D+1)
    (leafA : ∀v,∃i∈R,i≠v ∧ H.Adj a i)
    (leafB : ∀v,∃i∈R,i≠v ∧ H.Adj b i) : admits_matching_remainder H (D-1) := by
  classical
  let _ := Fintype.ofFinite R
  let f (i:R) := (H.neighborSet i.val∩K).ncard
  let A := {i:R | H.Adj a i.val}
  let B := {i:R | H.Adj b i.val}
  let S := {i:R | Nat.card (H.neighborSet i.val)=D-1}
  have total : (∑i,f i)≤D+1 := by simpa only [crossCount_eq_neighbor_sum] using roots
  have localBound (T : Finset R) : (∑i∈T,f i)≤D+1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (f:=f) (Finset.subset_univ T) (by intros;omega)).trans total
  have twoBound {i j : R} (ne : i≠j) : f i+f j≤D+1 := by
    simpa [ne] using localBound {i,j}
  have adjCases (i:R) (v:X) (edge : H.Adj i.val v) : v=a ∨ v=b ∨ v∈K := by
    rcases cover v with r|ra|rb|k
    · exact False.elim (ind i.property r edge.ne edge)
    · exact Or.inl ra
    · exact Or.inr (Or.inl rb)
    · exact Or.inr (Or.inr k)
  have fullLower (i:R) (hi:i∈S) : D-3≤f i := by
    let F := H.neighborSet i.val∩K
    have sub : H.neighborSet i.val ⊆ F∪{a,b} := by
      intro v edge
      rcases adjCases i v edge with ha|hb|k
      · exact Or.inr (Set.mem_insert_iff.mpr (Or.inl ha))
      · exact Or.inr (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hb)))
      · exact Or.inl ⟨edge,k⟩
    have h := (Set.ncard_le_ncard sub).trans (Set.ncard_union_le F {a,b})
    rw [Set.ncard_pair ab,←Nat.card_coe_set_eq,show Nat.card (H.neighborSet i.val)=D-1 from hi] at h
    change D-1≤f i+2 at h;omega
  have oneLower (i:R) (hi:i∈S) (s t:X)
      (restrict : ∀v,H.Adj i.val v → v=s ∨ v=t ∨ v∈K)
      (miss : ¬H.Adj s i.val) : D-2≤f i := by
    let F := H.neighborSet i.val∩K
    have sub : H.neighborSet i.val⊆F∪{t} := by
      intro v edge
      rcases restrict v edge with h|h|k
      · exact (miss (h ▸ edge.symm)).elim
      · exact Or.inr (Set.mem_singleton_iff.mpr h)
      · exact Or.inl ⟨edge,k⟩
    have h := (Set.ncard_le_ncard sub).trans (Set.ncard_union_le F {t})
    rw [Set.ncard_singleton,←Nat.card_coe_set_eq,show Nat.card (H.neighborSet i.val)=D-1 from hi] at h
    change D-1≤f i+1 at h;omega
  have reach (i:R) (hi:i∈S) : i∈A ∨ i∈B := by
    by_contra! neither
    have sub : H.neighborSet i.val ⊆ K := by
      intro v edge
      rcases adjCases i v edge with h|h|h
      · exact (neither.1 (show H.Adj a i.val from h ▸ edge.symm)).elim
      · exact (neither.2 (show H.Adj b i.val from h ▸ edge.symm)).elim
      · exact h
    have n := Set.ncard_le_ncard sub
    rw [←Nat.card_coe_set_eq,show Nat.card (H.neighborSet i.val)=D-1 from hi,order] at n
    omega
  have pA (i:R) (hi:i∈S) (j:R) (hj:j∈S) (ne:i≠j) : i∈A ∨ j∈A := by
    by_contra! wrong
    have l := oneLower i hi a b (adjCases i) wrong.1
    have r := oneLower j hj a b (adjCases j) wrong.2
    have sum := twoBound ne
    omega
  have rev (i:R) (v:X) (h:H.Adj i.val v) : v=b ∨ v=a ∨ v∈K := by
    rcases adjCases i v h with h|h|h <;> tauto
  have pB (i:R) (hi:i∈S) (j:R) (hj:j∈S) (ne:i≠j) : i∈B ∨ j∈B := by
    by_contra! wrong
    have l := oneLower i hi b a (rev i) wrong.1
    have r := oneLower j hj b a (rev j) wrong.2
    have sum := twoBound ne
    omega
  have all (i:R) (hi:i∈S) (j:R) (hj:j∈S) (ij:i≠j) (k:R) (hk:k∈S) : k=i ∨ k=j := by
    by_contra! other
    have l := fullLower i hi
    have r := fullLower j hj
    have t := fullLower k hk
    have sum := localBound {i,j,k}
    simp [ij,other.1.symm,other.2.symm] at sum
    omega
  obtain ⟨u,ur,_,ua⟩ := leafA a
  have non : A.Nonempty := ⟨⟨u,ur⟩,ua⟩
  have aChoices (v:R) : ∃w∈A,w≠v := by
    obtain ⟨z,zr,ne,h⟩ := leafA v.val
    exact ⟨⟨z,zr⟩,h,fun eq => ne (congrArg Subtype.val eq)⟩
  have bChoices (v:R) : ∃w∈B,w≠v := by
    obtain ⟨z,zr,ne,h⟩ := leafB v.val
    exact ⟨⟨z,zr⟩,h,fun eq => ne (congrArg Subtype.val eq)⟩
  obtain ⟨i,ai,j,bj,ne,assigned⟩ := assign_full_roots_to_leaves A B S non aChoices bChoices
    reach pA pB all
  have ik := fun mem => Set.disjoint_left.mp dis i.property mem
  have jk := fun mem => Set.disjoint_left.mp dis j.property mem
  have out (v:X) (hv:v∈({a,i.val,b,j.val} : Set X)) : v∉K := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with rfl|rfl|rfl|rfl <;> assumption
  have apart : Disjoint ({a,i.val} : Set X) {b,j.val} := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv hw
    rcases hv with rfl|rfl <;> rcases hw with hb|hj
    · exact ab hb
    · exact ar (hj.symm ▸ j.property)
    · exact br (hb ▸ i.property)
    · exact ne (Subtype.ext hj)
  obtain ⟨M,hm,km,av,bv,iv,jv⟩ := cover_even_clique_and_endpoints H K cl even a b i.val j.val
    ai bj out apart
  apply admits_remainder_of_full_cover H (D-1) (by omega) cap M hm
  intro v full
  rcases cover v with vr|eq|eq|vk
  · let z : R := ⟨v,vr⟩
    rcases assigned z full with h|h
    · have eq : v=i.val := congrArg Subtype.val h
      exact eq.symm ▸ iv
    · have eq : v=j.val := congrArg Subtype.val h
      exact eq.symm ▸ jv
  · exact eq.symm ▸ av
  · exact eq.symm ▸ bv
  · exact km vk

#print axioms path_clique_matching_remainder
end JSP452Audit.StarHost
