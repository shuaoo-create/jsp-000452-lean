import MatchingRankCenters
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem rank_twice_with_isolate (H : SimpleGraph X) (z : X)
    (isolate : ∀y,¬H.Adj z y) : 2*matchingEdges H+1≤Nat.card X := by
  obtain ⟨M,hm,maximum⟩ := exists_maximum_matching H
  have hz : z∉M.verts := by
    intro used
    obtain ⟨y,edge,_⟩ := hm used
    exact isolate y (M.adj_sub edge)
  have lower : 0<M.vertsᶜ.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨z,hz⟩
  have all := Set.ncard_add_ncard_compl M.verts
  rw [matching_vertices_eq_twice_edges hm,maximum] at all
  omega

private theorem rank_twice_le_order (H : SimpleGraph X) : 2*matchingEdges H≤Nat.card X := by
  obtain ⟨M,hm,maximum⟩ := exists_maximum_matching H
  have all := Set.ncard_add_ncard_compl M.verts
  rw [matching_vertices_eq_twice_edges hm,maximum] at all
  omega

/-- An isolated vertex outside the closed neighborhood of x has exactly the
same open neighborhood as x, by regularity. One neighbor of x therefore
takes care of every such isolate simultaneously. -/
private theorem outside_isolate_shares_neighbors (G : SimpleGraph X) (D : ℕ)
    (reg : ∀u,Nat.card (G.neighborSet u)=D) (x : X)
    (z : ↥((insert x (G.neighborSet x))ᶜ)) (iso :
      ∀y : ↥((insert x (G.neighborSet x))ᶜ),¬(G.induce (insert x (G.neighborSet x))ᶜ).Adj z y) :
    G.neighborSet z.val = G.neighborSet x := by
  have sub : G.neighborSet z.val⊆G.neighborSet x := by
    intro y zy
    by_contra notNeighbor
    have yne : y≠x := fun eq => z.property (Or.inr (eq ▸ (show G.Adj z.val y from zy)).symm)
    have outside : y∉insert x (G.neighborSet x) := fun h => h.elim yne notNeighbor
    exact iso ⟨y,outside⟩ zy
  apply Set.eq_of_subset_of_ncard_le sub
  rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq,reg,reg]

/-- In an odd-order even-regular component of degree at least four, save
one center compared with a near-perfect matching. Take x, dominate the
nonisolates outside its closed neighborhood, and share one neighbor of x
among any residual isolates. Even residual order accounts for that center. -/
theorem regular_centers_save_one [Nonempty X] (G : SimpleGraph X) (D : ℕ)
    (four : 4≤D) (evenD : Even D) (reg : ∀x,Nat.card (G.neighborSet x)=D)
    (crit : PerfectAfterEveryDeletion G) :
    ∃S : Set X,S.ncard<matchingEdges G ∧ ∀u,u∉S → ∃z∈S,G.Adj u z := by
  classical
  let x := Classical.choice ‹Nonempty X›
  let U : Set X := (insert x (G.neighborSet x))ᶜ
  let H := G.induce U
  have dx := reg x
  rw [Nat.card_coe_set_eq] at dx
  have un : U.ncard+D+1=Nat.card X := by
    have all := Set.ncard_add_ncard_compl (insert x (G.neighborSet x))
    rw [Set.ncard_insert_of_notMem (show x∉G.neighborSet x from G.loopless.irrefl x),dx] at all
    dsimp [U];omega
  have order := factorCritical_order_rank G crit x
  obtain ⟨j,ev⟩ := evenD
  obtain ⟨T,cost,dom⟩ := centers_at_matching_rank H
  let B : Set X := Subtype.val '' T
  have bc : B.ncard=T.ncard := Set.ncard_image_of_injective T Subtype.val_injective
  have base : (insert x B).ncard≤T.ncard+1 := (Set.ncard_insert_le x B).trans_eq (congrArg (fun n:ℕ => n+1) bc)
  have known (S : Set X) (xs : x∈S) (bs : B⊆S) (u : X) (out : u∉S)
      (special : ∀z : U,(∀y,¬H.Adj z y) → ∃v∈S,G.Adj z.val v) : ∃v∈S,G.Adj u v := by
    by_cases hu : u∈U
    · let z : U := ⟨u,hu⟩
      by_cases noniso : ∃y,H.Adj z y
      · have notT : z∉T := fun h => out (bs ⟨z,h,rfl⟩)
        obtain ⟨v,hv,adj⟩ := dom z noniso notT
        exact ⟨v.val,bs ⟨v,hv,rfl⟩,adj⟩
      · exact special z (fun y h => noniso ⟨y,h⟩)
    · have inside : u∈insert x (G.neighborSet x) := by by_contra h;exact hu h
      rcases inside with eq|adj
      · exact (out (eq ▸ xs)).elim
      · exact ⟨x,xs,(show G.Adj x u from adj).symm⟩
  by_cases exception : ∃z : U,∀y,¬H.Adj z y
  · obtain ⟨z,none⟩ := exception
    have extra := rank_twice_with_isolate H z none
    rw [Nat.card_coe_set_eq] at extra
    obtain ⟨p,hp⟩ := (Set.ncard_pos (Set.toFinite (G.neighborSet x))).mp (by omega)
    let S := insert p (insert x B)
    have sum := Set.ncard_insert_le p (insert x B)
    refine ⟨S,?_,fun u out => known S (Or.inr (Or.inl rfl))
      (fun _ h => Or.inr (Or.inr h)) u out ?_⟩
    · dsimp [S];omega
    · intro v vi
      have same := outside_isolate_shares_neighbors G D reg x v vi
      refine ⟨p,Or.inl rfl,?_⟩
      change p∈G.neighborSet v.val
      rw [same]
      exact hp
  · have upper := rank_twice_le_order H
    rw [Nat.card_coe_set_eq] at upper
    refine ⟨insert x B,by omega,fun u out => known _ (Or.inl rfl) (fun _ h => Or.inr h)
      u out (fun z h => (exception ⟨z,h⟩).elim)⟩

#print axioms regular_centers_save_one
end JSP452Audit.StarHost
