import PairFamily

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Keep every old edge whose endpoints survive, and match the freed pairs of
endpoints simultaneously. The resulting support is exactly the surviving old support. -/
theorem simultaneous_cut_repair {X J : Type*} (G : SimpleGraph X) (M : G.Subgraph)
    (hm : M.IsMatching) (I : Set X) (a y : J ↪ X) (b z : J → X)
    (apart : Disjoint (Set.range a) (Set.range y))
    (ab : ∀ i, M.Adj (a i) (b i)) (yz : ∀ i, M.Adj (y i) (z i))
    (ay : ∀ i, G.Adj (a i) (y i))
    (bin : ∀ i, b i∈I) (zin : ∀ i, z i∈I) (aout : ∀ i, a i∉I) (yout : ∀ i, y i∉I)
    (cut : M.verts ∩ I ⊆ Set.range b ∪ Set.range z) :
    ∃ N : (G.induce Iᶜ).Subgraph, N.IsMatching ∧ ∀ v : ↥Iᶜ, v∈N.verts ↔ v.val∈M.verts := by
  classical
  let H := G.induce Iᶜ
  let K : H.Subgraph := {
    verts := {u | ∃ v : ↥Iᶜ, M.Adj u.val v.val}
    Adj := fun u v => M.Adj u.val v.val
    adj_sub := fun e => M.adj_sub e
    edge_vert := fun e => ⟨_,e⟩
    symm := ⟨fun _ _ e => e.symm⟩ }
  have matchK : K.IsMatching := by
    rintro u ⟨v,uv⟩
    exact ⟨v,uv,fun w uw => Subtype.ext (hm.eq_of_adj_left uw uv)⟩
  let l : J ↪ ↥Iᶜ := ⟨fun i => ⟨a i,aout i⟩,fun _ _ h => a.injective (congrArg Subtype.val h)⟩
  let r : J ↪ ↥Iᶜ := ⟨fun i => ⟨y i,yout i⟩,fun _ _ h => y.injective (congrArg Subtype.val h)⟩
  have edge (i : J) : H.Adj (l i) (r i) := ay i
  let P := Padded.pairFamily H l r edge
  have lr : Disjoint (Set.range l) (Set.range r) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨i,rfl⟩ ⟨j,eq⟩
    exact apart.ne_of_mem (Set.mem_range_self i) (Set.mem_range_self j) (congrArg Subtype.val eq.symm)
  have dis : Disjoint K.verts P.verts := by
    apply Set.disjoint_left.mpr
    rintro u ⟨v,uv⟩ (⟨i,rfl⟩|⟨i,rfl⟩)
    · have same := hm.eq_of_adj_left uv (ab i)
      exact v.property (same ▸ bin i)
    · have same := hm.eq_of_adj_left uv (yz i)
      exact v.property (same ▸ zin i)
  refine ⟨K⊔P,Padded.matching_sup_of_disjoint_verts H matchK (Padded.pairFamily_isMatching H l r edge lr) dis,?_⟩
  intro v
  constructor
  · rintro (⟨w,vw⟩|⟨i,rfl⟩|⟨i,rfl⟩)
    · exact M.edge_vert vw
    · exact M.edge_vert (ab i)
    · exact M.edge_vert (yz i)
  · intro hv
    obtain ⟨w,vw,_⟩ := hm hv
    by_cases lost : w∈I
    · rcases cut ⟨M.edge_vert vw.symm,lost⟩ with ⟨i,rfl⟩|⟨i,rfl⟩
      · exact Or.inr (Or.inl ⟨i,Subtype.ext (hm.eq_of_adj_right (ab i) vw)⟩)
      · exact Or.inr (Or.inr ⟨i,Subtype.ext (hm.eq_of_adj_right (yz i) vw)⟩)
    · exact Or.inl ⟨⟨w,lost⟩,vw⟩

#print axioms simultaneous_cut_repair
end JSP452Audit.StarHost
