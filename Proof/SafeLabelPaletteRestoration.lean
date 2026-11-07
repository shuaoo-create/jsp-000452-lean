import MatchedAndLabelledResidualDegrees
namespace JSP452Audit.StarHost.FiveExposureLabels
open SimpleGraph
variable {X:Type*} [Finite X] {G:SimpleGraph X} (L:FiveExposureLabels G)

theorem selected_union (A B:Set ↥L.W) : L.selected (A∪B)=L.selected A⊔L.selected B := by
  ext x y
  constructor
  · rintro (⟨u,h,r,t⟩|⟨u,h,r,t⟩)
    · rcases h with a|b
      · exact Or.inl (Or.inl ⟨u,a,r,t⟩)
      · exact Or.inr (Or.inl ⟨u,b,r,t⟩)
    · rcases h with a|b
      · exact Or.inl (Or.inr ⟨u,a,r,t⟩)
      · exact Or.inr (Or.inr ⟨u,b,r,t⟩)
  · rintro ((⟨u,h,r,t⟩|⟨u,h,r,t⟩)|(⟨u,h,r,t⟩|⟨u,h,r,t⟩))
    · exact Or.inl ⟨u,Or.inl h,r,t⟩
    · exact Or.inr ⟨u,Or.inl h,r,t⟩
    · exact Or.inl ⟨u,Or.inr h,r,t⟩
    · exact Or.inr ⟨u,Or.inr h,r,t⟩

theorem selected_hits_label (A:Set ↥L.W) {x y:X} (edge:(L.selected A).Adj x y) :
    x∈Subtype.val '' A ∨ y∈Subtype.val '' A := by
  rcases edge with ⟨u,h,eq,_⟩|⟨u,h,eq,_⟩
  · exact Or.inl ⟨u,h,eq⟩
  · exact Or.inr ⟨u,h,eq⟩

omit [Finite X] in
private theorem joined_degree_le (Q R:SimpleGraph X) (v:X) :
    ((Q⊔R).neighborSet v).ncard≤(Q.neighborSet v).ncard+(R.neighborSet v).ncard :=
  Set.ncard_union_le _ _

theorem safe_red_degree (R:SimpleGraph X) (A:Set ↥L.W)
    (safe:∀v,(R.neighborSet v).ncard+(L.fiber A v).ncard≤2) :
    ∀v,Nat.card (((L.M.spanningCoe⊔R)⊔L.selected A).neighborSet v)≤3 := by
  intro v
  have p := joined_degree_le (L.M.spanningCoe⊔R) (L.selected A) v
  have q := joined_degree_le L.M.spanningCoe R v
  have slack := safe v
  change (((L.M.spanningCoe⊔R)⊔L.selected A).neighborSet v).ncard≤3
  by_cases hit:v∈L.M.verts
  · have one : (L.M.spanningCoe.neighborSet v).ncard≤1 := spanningMatching_degree_le_one L.M L.matching v
    rw [L.selected_at_matched A hit,Set.ncard_image_of_injective _ Subtype.val_injective] at p
    omega
  · have none : L.M.spanningCoe.neighborSet v=∅ := Set.eq_empty_of_forall_notMem (fun _ e => hit (L.M.edge_vert e))
    rw [none,Set.ncard_empty] at q
    have one := L.selected_unmatched_degree A hit
    omega

theorem actual_labels_force_complement (R:SimpleGraph X) (sub:R≤L.base) (A:Set ↥L.W)
    (safe:∀v,(R.neighborSet v).ncard+(L.fiber A v).ncard≤2)
    (blue:∀v,Nat.card ((L.base \ R).neighborSet v)≤2) (u v:ℕ) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => 4)) (forest (fun _:Fin v => 3))) :
    u+v-1≤Aᶜ.ncard := by
  classical
  by_contra! small
  obtain ⟨J,B,parts,_,redLim,blueLim⟩ := split_control_budget Aᶜ hu hv small
  let P := (L.M.spanningCoe⊔R)⊔L.selected A
  let finalRed := P⊔L.selected J
  have incl : finalRed≤G := sup_le (sup_le (sup_le L.M.spanningCoe_le (sub.trans sdiff_le)) (L.selected_sub _)) (L.selected_sub _)
  have all : A∪J∪B=Set.univ := by rw [Set.union_assoc,parts,Set.union_compl_self]
  have edges := congrArg L.selected all
  rw [L.selected_union,L.selected_union] at edges
  rcases force finalRed incl with reds|blues
  · have hits {x y:X} (edge:finalRed.Adj x y) : x∈Subtype.val '' J ∨ y∈Subtype.val '' J ∨ P.Adj x y := by
      rcases edge with basic|marked
      · exact Or.inr (Or.inr basic)
      · exact (L.selected_hits_label J marked).elim Or.inl (fun h => Or.inr (Or.inl h))
    have bound := count_large_of_edge_cover finalRed P (Subtype.val '' J) 3 (fun _:Fin u => 4) (fun {_ _} h => hits h) (L.safe_red_degree R A safe) reds
    simp only [Set.ncard_image_of_injective _ Subtype.val_injective] at bound
    have count : (Finset.univ.filter (fun _:Fin u => 3+1≤4)).card=u := by simp
    rw [count] at bound;omega
  · have cover {x y:X} (edge:(G \ finalRed).Adj x y) :
        x∈Subtype.val '' B ∨ y∈Subtype.val '' B ∨ (L.base \ R).Adj x y := by
      by_cases old : (L.M.spanningCoe⊔L.selected Set.univ).Adj x y
      · rcases old with mat|sel
        · exact (edge.2 (Or.inl (Or.inl (Or.inl mat)))).elim
        · rw [←edges] at sel
          rcases sel with (a|j)|b
          · exact (edge.2 (Or.inl (Or.inr a))).elim
          · exact (edge.2 (Or.inr j)).elim
          · exact (L.selected_hits_label B b).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr ⟨⟨edge.1,old⟩,fun h => edge.2 (Or.inl (Or.inl (Or.inr h)))⟩)
    have bound := count_large_of_edge_cover (G \ finalRed) (L.base \ R) (Subtype.val '' B) 2
      (fun _:Fin v => 3) (fun {_ _} h => cover h) blue blues
    simp only [Set.ncard_image_of_injective _ Subtype.val_injective] at bound
    have count : (Finset.univ.filter (fun _:Fin v => 2+1≤3)).card=v := by simp
    rw [count] at bound;omega

#print axioms selected_union
#print axioms selected_hits_label
#print axioms safe_red_degree
#print axioms actual_labels_force_complement
end JSP452Audit.StarHost.FiveExposureLabels
