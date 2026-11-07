import TheRealTopPairRefundIsPaidOnTheVerySameSmallerRow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
namespace JSP452Audit.StarHost

/-- Count five-way independent labels under a restriction on a finite set.
No probabilistic independence of graph vertices is assumed. -/
theorem fifth_mask_count {X : Type*} [Finite X] (S : Set X) (P : Fin 5→Prop) :
    Nat.card {f : X→Fin 5 // ∀x∈S,P (f x)} =
      Nat.card {y : Fin 5 // P y}^S.ncard * 5^Sᶜ.ncard := by
  classical
  let F := {f : X→Fin 5 // ∀x∈S,P (f x)}
  let V := {y : Fin 5 // P y}
  let encode (f:F) : (S→V) × (↥(Sᶜ : Set X)→Fin 5) := (fun x => ⟨f.val x.val,f.property _ x.property⟩,fun x => f.val x.val)
  let decode (g:(S→V) × (↥(Sᶜ : Set X)→Fin 5)) (x:X) := if hx:x∈S then (g.1 ⟨x,hx⟩).val else g.2 ⟨x,hx⟩
  let e : F ≃ (S→V) × (↥(Sᶜ : Set X)→Fin 5) := {
    toFun := encode
    invFun := fun g => ⟨decode g,fun x hx => by simp only [decode,dif_pos hx];exact (g.1 ⟨x,hx⟩).property⟩
    left_inv := fun f => by apply Subtype.ext;funext x;by_cases hx:x∈S <;> simp [decode,encode,hx]
    right_inv := fun g => by
      apply Prod.ext
      · funext x;apply Subtype.ext;simp [encode,decode,x.property]
      · funext x;simp [encode,decode,(show x.val∉S from x.property)] }
  have h := Nat.card_congr e
  rw [Nat.card_prod,Nat.card_fun,Nat.card_fun,Nat.card_fin,Nat.card_coe_set_eq,Nat.card_coe_set_eq] at h
  exact h

theorem fifth_mask_weight {X : Type*} [Finite X] (S : Set X) (P : Fin 5→Prop) :
    (Nat.card {f : X→Fin 5 // ∀x∈S,P (f x)} : ℚ) =
      (5:ℚ)^(Nat.card X)*((Nat.card {y : Fin 5 // P y}:ℚ)/5)^S.ncard := by
  rw [fifth_mask_count]
  have order := Set.ncard_add_ncard_compl S
  rw [←order,pow_add,div_pow]
  push_cast
  field_simp

theorem missed_fifth_weight {X : Type*} [Finite X] (S : Set X) :
    (Nat.card {f : X→Fin 5 // ∀x∈S,f x≠0} : ℚ) =
      (5:ℚ)^(Nat.card X)*(4/5:ℚ)^S.ncard := by
  have count : Nat.card {y : Fin 5 // y≠0}=4 := by rw [Nat.card_eq_fintype_card];decide
  have eq := fifth_mask_weight S (fun y : Fin 5 => y≠0)
  rw [count] at eq;exact eq

theorem selected_fifth_weight {X : Type*} [Finite X] (v:X) :
    (Nat.card {f : X→Fin 5 // f v=0} : ℚ)=(5:ℚ)^(Nat.card X)/5 := by
  have count : Nat.card {y : Fin 5 // y=0}=1 := by rw [Nat.card_eq_fintype_card];decide
  have weight := fifth_mask_weight ({v}:Set X) (fun y => y=0)
  have eq : {f:X→Fin 5 | ∀x∈({v}:Set X),f x=0}={f | f v=0} := by ext f;simp
  change ((Nat.card ↥({f:X→Fin 5 | ∀x∈({v}:Set X),f x=0}:Set (X→Fin 5))):ℚ)=_ at weight
  rw [eq,count,Set.ncard_singleton,pow_one] at weight
  change (Nat.card {f:X→Fin 5 // f v=0}:ℚ)=(5:ℚ)^(Nat.card X)*(1/5) at weight
  simpa only [div_eq_mul_inv,one_mul] using weight

#print axioms fifth_mask_count
#print axioms missed_fifth_weight
#print axioms selected_fifth_weight
end JSP452Audit.StarHost
