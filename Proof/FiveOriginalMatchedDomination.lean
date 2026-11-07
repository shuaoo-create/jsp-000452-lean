import FiveMatchedInteriorDominatingSet
import DominatingBlueEndpoint
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem cross_transfer (G : SimpleGraph X) (T B A C : Set X)
    (land : ∀v∈T,∀w∈B,G.Adj v w → v∈A ∧ w∈C) :
    crossCount G T B≤crossCount G A C := by
  let L := {p : (↥T × ↥B) // G.Adj p.1.val p.2.val}
  let R := {p : (↥A × ↥C) // G.Adj p.1.val p.2.val}
  have inc (p:L) := land _ p.val.1.property _ p.val.2.property p.property
  let f (p:L) : R := ⟨(⟨p.val.1.val,(inc p).1⟩,⟨p.val.2.val,(inc p).2⟩),p.property⟩
  apply Nat.card_le_card_of_injective f
  intro p q eq
  exact Subtype.ext (Prod.ext (Subtype.ext (congrArg (fun v:R => v.val.1.val) eq))
    (Subtype.ext (congrArg (fun v:R => v.val.2.val) eq)))

private theorem cross_budget_split (G : SimpleGraph X) (A B S : Set X) (sub : S⊆B) :
    crossCount G A (B\S)+crossCount G S A=crossCount G A B := by
  classical
  let _ := Fintype.ofFinite A
  rw [crossCount_swap G S A]
  simp only [crossCount_eq_neighbor_sum]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro v _
  let N := G.neighborSet v.val
  have eq : (N∩(B\S))∪(N∩S)=N∩B := by rw [←Set.inter_union_distrib_left,Set.sdiff_union_of_subset sub]
  have dis : Disjoint (N∩(B\S)) (N∩S) := Set.disjoint_left.mpr (fun _ h hs => h.2.2 hs.2)
  exact ((Set.ncard_union_eq dis).symm.trans (congrArg Set.ncard eq))

/-- The actual maximum matching in the five-degree original core supplies
exactly two discounted labels per matched edge. No exterior edge is counted twice. -/
theorem five_original_matched_domination (G : SimpleGraph X) (K : DegreeRegion G 5) :
    ∃S:Set X,(∀v,Nat.card (G.neighborSet v)=5 → v∈S ∨ ∃w∈S,G.Adj v w) ∧
      4*(S.ncard:ℚ)+(8/50:ℚ)*matchingEdges (G.induce K.core) ≤
        4*(21/50:ℚ)*((2*(K.roots.ncard+matchingEdges (G.induce K.core))+minimumExposure G 5:ℕ):ℚ)+
        (((G.induce K.rest).edgeSet.ncard-matchingEdges (G.induce K.rest):ℕ):ℚ)+
        (crossCount G K.roots K.rest:ℚ) := by
  classical
  let Y := K.core∪K.roots
  let B := K.rest
  let A := K.roots
  obtain ⟨ap,ab,pb,all⟩ := region_partition G K.barrier K.pieces
  change Disjoint A K.core at ap
  change Disjoint A B at ab
  change Disjoint K.core B at pb
  change (A∪K.core)∪B=Set.univ at all
  have cover : Y∪B=Set.univ := by rwa [Set.union_comm A K.core] at all
  have dis : Disjoint Y B := Set.disjoint_union_left.mpr ⟨pb,ab⟩
  have split := (core_rest_partition G K.barrier K.pieces).2.2
  obtain ⟨S,inside,full,ind,dom⟩ := choose_full_exterior_independent G B 5
  have boundary (v:X) (hv:v∈S) (w:X) (e:G.Adj v w) : w∈B ∨ w∈A := by
    rcases (show w∈Y∪B from cover.symm ▸ Set.mem_univ w) with (core|root)|rest
    · exact (split core (inside hv) e.symm).elim
    · exact Or.inr root
    · exact Or.inl rest
  have external := exterior_independent_degree_price G B A S ab.symm inside ind 5 (by decide) full boundary
  let T := {v | v∈Y ∧ Nat.card (G.neighborSet v)=5 ∧ v∉S ∧ ∀w∈S,¬G.Adj v w}
  obtain ⟨J,hm,max⟩ := exists_maximum_matching (G.induce K.core)
  let inc : (G.induce K.core).Copy (G.induce Y) :=
    ⟨⟨fun z => ⟨z.val,Or.inl z.property⟩,fun edge => edge⟩,fun _ _ eq =>
      Subtype.ext (congrArg (fun z:Y => z.val) eq)⟩
  let M := J.map inc.toHom
  have matched : M.IsMatching := hm.map inc.toHom inc.injective
  have support : M.verts.ncard=2*matchingEdges (G.induce K.core) := by
    change (inc.toHom '' J.verts).ncard=_
    rw [Set.ncard_image_of_injective _ inc.injective,matching_vertices_eq_twice_edges hm,max]
  have inCore (v:Y) (hv:v∈M.verts) : v.val∈K.core := by
    obtain ⟨z,_,rfl⟩ := hv;exact z.property
  have closed (v:Y) (hv:v∈M.verts) (w:X) (hw:w∈B) := split (inCore v hv) hw
  have land (v:Y) (hv:v∈M.verts) : v.val∈T := by
    have insideCore := inCore v hv
    have degree := regionCore_full_degree G K.barrier K.pieces 5 K.full insideCore
    exact ⟨v.property,degree,fun vs => (pb.ne_of_mem insideCore (inside vs)) rfl,
      fun w hw => closed v hv w (inside hw)⟩
  obtain ⟨P,inY,hit,fee⟩ := five_dominate_with_matching G Y B T dis cover (fun _ h => h.1)
    (fun _ h => h.2.1) M matched land closed
  have transfer := cross_transfer G T B A (B\S) (by
    intro v hv w wb e
    refine ⟨hv.1.resolve_left (fun hp => split hp wb e),wb,fun ws => hv.2.2.2 w ws e⟩)
  have budget := cross_budget_split G A B S inside
  have cross : crossCount G T B+crossCount G S A≤crossCount G A B := by omega
  have size : Y.ncard=2*(A.ncard+matchingEdges (G.induce K.core))+minimumExposure G 5 := by
    change (K.core∪A).ncard=_
    rw [Set.ncard_union_eq ap.symm,K.core_order];dsimp [A];omega
  have er : 4*(S.ncard:ℚ)≤(((G.induce B).edgeSet.ncard-matchingEdges (G.induce B):ℕ):ℚ)+(crossCount G S A:ℚ) := by
    change 4*S.ncard≤(G.induce B).edgeSet.ncard-matchingEdges (G.induce B)+crossCount G S A at external
    exact_mod_cast external
  have cq : (crossCount G T B:ℚ)+crossCount G S A≤crossCount G A B := by exact_mod_cast cross
  refine ⟨P∪S,?_,?_⟩
  · intro v vd
    rcases (show v∈Y∪B from cover.symm ▸ Set.mem_univ v) with vy|vb
    · by_cases yes : v∈S
      · exact Or.inl (Or.inr yes)
      by_cases next : ∃w∈S,G.Adj v w
      · obtain ⟨w,ws,e⟩ := next;exact Or.inr ⟨w,Or.inr ws,e⟩
      have vT : v∈T := ⟨vy,vd,yes,fun w ws e => next ⟨w,ws,e⟩⟩
      rcases hit v vT with p|⟨w,wp,e⟩
      · exact Or.inl (Or.inl p)
      · exact Or.inr ⟨w,Or.inl wp,e⟩
    · rcases dom v vb vd with vs|⟨w,ws,e⟩
      · exact Or.inl (Or.inr vs)
      · exact Or.inr ⟨w,Or.inr ws,e⟩
  · rw [Set.ncard_union_eq (dis.mono inY inside),Nat.cast_add, mul_add]
    rw [size,support,Nat.cast_mul,Nat.cast_ofNat] at fee
    change _ ≤ _ + (((G.induce B).edgeSet.ncard-matchingEdges (G.induce B):ℕ):ℚ)+(crossCount G A B:ℚ)
    linarith

/-- The original red full head forces the length of the blue suffix, now
with the discount from the very same maximum core matching. -/
theorem five_original_matched_blue_price {s t r : ℕ} (G : SimpleGraph X) (K : DegreeRegion G 5)
    (hs : 0<s) (n : Fin s→ℕ) (m : Fin t→ℕ) (pm : ∀j,1≤m j)
    (cap : ∀v,Nat.card (G.neighborSet v)≤5) (head : n ⟨0,hs⟩=5) (active : r<t)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    4*((t-r:ℕ):ℚ)+(8/50:ℚ)*matchingEdges (G.induce K.core) ≤
      4*(21/50:ℚ)*((2*(K.roots.ncard+matchingEdges (G.induce K.core))+minimumExposure G 5:ℕ):ℚ)+
      (((G.induce K.rest).edgeSet.ncard-matchingEdges (G.induce K.rest):ℕ):ℚ)+(crossCount G K.roots K.rest:ℚ) := by
  obtain ⟨S,dom,price⟩ := five_original_matched_domination G K
  have need := dominating_set_pays_blue_suffix G 5 (by decide) hs n m pm cap head active row S dom
  have q : ((t-r:ℕ):ℚ)≤S.ncard := by exact_mod_cast need
  linarith

#print axioms five_original_matched_domination
#print axioms five_original_matched_blue_price
end JSP452Audit.StarHost
