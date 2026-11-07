import RetainedPathMatching
import ZeroReserveIndependentCuts
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The deletion and matching live on the original graph. All singleton holes,
the unique portal, and one chosen companion vertex account for |I|−1 points. -/
theorem three_path_original_witness (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (six : 6≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (s : ThreePathShape (Q.induce Iᶜ) D) (count : s.singles.ncard+3=I.ncard) :
    ∃ U : Set X, U.ncard+1=I.ncard ∧ admits_matching_remainder (Q.induce Uᶜ) (D-1) := by
  classical
  let S := Subtype.val '' s.singles
  let C := Subtype.val '' s.companion
  let a := s.left.val
  let b := s.right.val
  let x := s.pivot.val
  have free (v : ↥(Iᶜ : Set X)) (hp : v∈({s.pivot,s.left,s.right} : Set ↥(Iᶜ : Set X))) :
      v.val∉S ∧ v.val∉C := by
    obtain ⟨hs,hc⟩ := s.path_free v hp
    constructor
    · rintro ⟨w,hw,h⟩;exact hs ((Subtype.ext h : w=v) ▸ hw)
    · rintro ⟨w,hw,h⟩;exact hc ((Subtype.ext h : w=v) ▸ hw)
  have fa : a∉S ∧ a∉C := free s.left (by simp)
  have fb : b∉S ∧ b∉C := free s.right (by simp)
  have fx : x∉S ∧ x∉C := free s.pivot (by simp)
  have ab : a≠b := fun e => s.different (Subtype.ext e)
  have ax : a≠x := fun e => s.left_off (Subtype.ext e)
  have bx : b≠x := fun e => s.right_off (Subtype.ext e)
  have sc : Disjoint S C := Set.disjoint_image_of_injective Subtype.val_injective s.clean
  have ci : Disjoint I C := by
    apply Set.disjoint_left.mpr
    rintro _ hi ⟨v,_,rfl⟩
    exact v.property hi
  have csize := (Set.ncard_image_of_injective s.companion Subtype.val_injective).trans s.clique_order
  have clique : Q.IsClique C := by
    rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne
    exact s.clique hv hw (fun eq => ne (congrArg Subtype.val eq))
  have cn : C.Nonempty := (Set.ncard_pos (Set.toFinite _)).mp
    (show 0<C.ncard from (by change 0<(Subtype.val '' s.companion).ncard;omega))
  have charge := three_path_companion_root_cap Q I ind largest D six reg s count
  obtain ⟨z,zc,zcap⟩ := select_original_companion_vertex Q I C a b D six ind reg ab fa.2 fb.2 cn charge
  let T := I∪{a,b}∪(C\{z})
  have xt : x∉T := by
    rintro ((hi|h)|hc)
    · exact s.pivot.property hi
    · rcases Set.mem_insert_iff.mp h with ha|hb
      · exact ax ha.symm
      · exact bx (Set.mem_singleton_iff.mp hb).symm
    · exact fx.2 hc.1
  have zt : z∉T := by
    rintro ((hi|h)|hc)
    · exact Set.disjoint_left.mp ci hi zc
    · rcases Set.mem_insert_iff.mp h with ha|hb
      · exact fa.2 (ha ▸ zc)
      · exact fb.2 ((Set.mem_singleton_iff.mp hb) ▸ zc)
    · exact hc.2 (by simp)
  have ss (v:X) (hs:v∈S) : v∉T := by
    rintro ((hi|h)|hc)
    · obtain ⟨w,_,rfl⟩ := hs
      exact w.property hi
    · rcases Set.mem_insert_iff.mp h with ha|hb
      · exact fa.1 (ha ▸ hs)
      · exact fb.1 ((Set.mem_singleton_iff.mp hb) ▸ hs)
    · exact Set.disjoint_left.mp sc hs hc.1
  have split : Tᶜ=S∪{x,z} := by
    ext v
    constructor
    · intro vt
      have vi : v∉I := fun h => vt (Or.inl (Or.inl h))
      let w : ↥(Iᶜ : Set X) := ⟨v,vi⟩
      rcases s.cover w with h|h|h|h|h
      · exact Or.inl ⟨w,h,rfl⟩
      · by_cases vz : v=z
        · exact Or.inr (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr vz)))
        · exact (vt (Or.inr ⟨⟨w,h,rfl⟩,by simpa using vz⟩)).elim
      · exact Or.inr (Set.mem_insert_iff.mpr (Or.inl (congrArg Subtype.val h)))
      · exact (vt (Or.inl (Or.inr (Set.mem_insert_iff.mpr (Or.inl (congrArg Subtype.val h)))))).elim
      · exact (vt (Or.inl (Or.inr (Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mpr (congrArg Subtype.val h))))))).elim
    · rintro (hs|h)
      · exact ss v hs
      · rcases Set.mem_insert_iff.mp h with ha|hb
        · exact ha.symm ▸ xt
        · exact (Set.mem_singleton_iff.mp hb).symm ▸ zt
  have sep : Disjoint S ({x,z} : Set X) := by
    apply Set.disjoint_left.mpr
    intro v hs h
    rcases Set.mem_insert_iff.mp h with ha|hb
    · exact fx.1 (ha ▸ hs)
    · exact Set.disjoint_left.mp sc ((Set.mem_singleton_iff.mp hb) ▸ hs) zc
  have size : Tᶜ.ncard+1=I.ncard := by
    rw [split,Set.ncard_union_eq sep,Set.ncard_pair (show x≠z from fun eq => fx.2 (eq.symm ▸ zc)),
      show S.ncard=s.singles.ncard from Set.ncard_image_of_injective _ Subtype.val_injective]
    omega
  have leaf (v : ↥(Iᶜ : Set X)) (h : (Q.induce Iᶜ).neighborSet v={s.pivot}) :
      Q.Adj x v.val ∧ (Q.neighborSet v.val∩I).ncard=D-1 := by
    have adj : s.pivot∈(Q.induce Iᶜ).neighborSet v := h.symm ▸ Set.mem_singleton _
    have d := degree_to_root_and_residual Q I v
    rw [h,Nat.card_coe_set_eq,Set.ncard_singleton,reg] at d
    exact ⟨(show (Q.induce Iᶜ).Adj v s.pivot from adj).symm,by omega⟩
  have lh := leaf s.left s.left_neighbors
  have rh := leaf s.right s.right_neighbors
  have witness := retained_path_remainder Q I C a b x z D six par reg ind ci ab
    s.left.property s.right.property fa.2 fb.2 zc clique csize charge lh.1 rh.1 lh.2 rh.2 xt zcap
  refine ⟨Tᶜ,size,?_⟩
  rw [show Tᶜᶜ=T by ext v; simp]; exact witness

#print axioms three_path_original_witness
end JSP452Audit.StarHost
