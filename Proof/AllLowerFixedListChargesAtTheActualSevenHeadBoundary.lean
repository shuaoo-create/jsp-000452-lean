import EveryPositiveProtectedAllowanceOnAnActualPayableExteriorPrefix
namespace JSP452Audit.StarHost

theorem four_five_pair_fee (Z N H j x y:ℕ) (ratio:11*N≤24*Z) (head:7≤H)
    (px:0<x) (py:0<y) (xt:x≤H) (yt:y≤H) (col:x+y=j+2) :
    N/6+fixedHeadLoss Z N (N/6) x+fixedHeadLoss Z N (N/6) y≤middleColumnFee Z N H j := by
  let l := N/6
  let M (v:ℕ) := min Z (N/(v+1))
  have bounded (v w:ℕ) (lo:w≤v) : M v≤N/(w+1) := (Nat.min_le_right _ _).trans
    (Nat.div_le_div_left (Nat.add_le_add_right lo 1) (by omega))
  have zero (v:ℕ) (lo:5≤v) : M v≤l := bounded v 5 lo
  have base (v:ℕ) : M v≤Z := Nat.min_le_left _ _
  have lz : l≤Z := by dsimp [l];omega
  change l+(M x-l)+(M y-l)≤_
  unfold middleColumnFee
  split_ifs with first short lower near
  · have a := base x;have b := base y;change _≤2*Z-l;omega
  · have enough : l≤N/(j+2) := Nat.div_le_div_left (by omega) (by omega)
    by_cases xu:x=1
    · have eq : y+1=j+2 := by omega
      have hy := (Nat.min_le_right Z (N/(y+1)));change M y≤_ at hy;rw [eq] at hy
      have hx := base x
      omega
    by_cases yu:y=1
    · have eq : x+1=j+2 := by omega
      have hx := (Nat.min_le_right Z (N/(x+1)));change M x≤_ at hx;rw [eq] at hx
      have hy := base y
      omega
    have a := bounded x 2 (by omega)
    have b := bounded y 2 (by omega)
    have cap : N/5≤N/(j+2) := Nat.div_le_div_left (by omega) (by omega)
    by_cases three:j=2
    · have eq : N/(j+2)=N/4 := by rw [three]
      dsimp only [l] at *;omega
    · rcases (show 3≤x ∨ 3≤y by omega) with hi|hi
      · have tighter := bounded x 3 hi;dsimp only [l] at *;omega
      · have tighter := bounded y 3 hi;dsimp only [l] at *;omega
  · by_cases large:5≤x ∨ 5≤y
    · rcases large with one|two
      · have a := zero x one;have b := base y;omega
      · have b := zero y two;have a := base x;omega
    have both : 2≤x ∧ 2≤y := by omega
    have a := bounded x 2 both.1
    have b := bounded y 2 both.2
    rcases (show 3≤x ∨ 3≤y by omega) with hi|hi
    · have c := bounded x 3 hi;dsimp only [l] at *;omega
    · have c := bounded y 3 hi;dsimp only [l] at *;omega
  · have a : j-H+2≤x := by omega
    have b : j-H+2≤y := by omega
    have capX := bounded x _ a
    have capY := bounded y _ b
    change M x≤N/(j-H+3) at capX
    change M y≤N/(j-H+3) at capY
    have spare : l≤N/(j-H+3) := Nat.div_le_div_left (by omega) (by omega)
    rcases (show 5≤x ∨ 5≤y by omega) with one|two
    · have calm := zero x one;omega
    · have calm := zero y two;omega
  · have a := zero x (by omega)
    have b := zero y (by omega)
    change _≤l;omega

#print axioms four_five_pair_fee
end JSP452Audit.StarHost
