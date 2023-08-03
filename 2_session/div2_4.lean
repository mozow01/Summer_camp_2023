import Mathlib

theorem hatvanyok_1 : ∀ n : ℕ , 10 ∣ (7^(2*n+1) + 3^(2*n+1)) := by
intros n
induction n
case zero =>
     norm_num
case succ n ih =>
     have h7 : 7^(2*(n+1)+1) = 49 * 7^(2*n+1) := by ring
     -- by calc 
          -- 7^(2*(n+1)+1) = 7^((2*n+1)+2)           := by rfl
          -- _ = 7^2 * 7^(2*n+1)                     := by exact Nat.pow_add' 7 (2 * n + 1) 2
          -- _ = 49 * 7^(2*n+1)                      := by rfl
     have h3 : 3^(2*(n+1)+1) =  9 * 3^(2*n+1) := by ring
     rw [h7,h3]
     have h40 : 49 * 7^(2*n+1) + 9 * 3^(2*n+1) = 4*(10*7^(2*n+1)) + 9*(7^(2*n+1) + 3^(2*n+1)) := by ring
     rw [h40]
     apply Dvd.dvd.linear_comb
     exact Nat.dvd_mul_right 10 (7 ^ (2 * n + 1))
     assumption


theorem warmup : ∀ n : ℕ , 7^n ≡ 3^n [MOD 4] := by
intro n
exact Nat.ModEq.pow n rfl

-- theorem hatvanyok_2 : ∀ n : ℕ , 7^(2*n+1) + 3^(2*n+1) ≡ 0 [MOD 10] := by
-- intros n
-- repeat rw [pow_add]
-- norm_num
-- repeat rw [pow_mul]
-- norm_num
-- have h1 : 49^n ≡ 9^n [MOD 10] := by exact Nat.ModEq.pow n rfl
-- have h2 : 49^n * 7 ≡ 9^n * 7 [MOD 10] := by exact Nat.ModEq.mul h1 rfl
-- have h3 : 49^n * 7 + 9^n * 3 ≡ 9^n * 7 + 9^n * 3 [MOD 10] := by exact Nat.ModEq.add h2 rfl
-- have h4 :  9^n * 7 + 9^n * 3 ≡ 0 [MOD 10] := by
--      ring_nf
--      exact Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_left 10 (9 ^ n))
-- exact Nat.ModEq.trans h3 h4

theorem hatvanyok_3 : ∀ n : ℕ , 7^(2*n+1) + 3^(2*n+1) ≡ 0 [MOD 10] := by
     intros n
     refine Dvd.dvd.modEq_zero_nat ?h
     apply hatvanyok_1
     --apply Nat.modEq_zero_iff_dvd.mpr
     --apply hatvanyok_1