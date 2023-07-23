import data.nat.basic
import data.nat.pow
import tactic.linarith
import data.nat.modeq
import tactic.norm_num

theorem hatvanyok_1 : ∀ n : ℕ , 10 ∣ (7^(2*n+1) + 3^(2*n+1)):=
begin
intros n,
induction n,
norm_num,
have lem : 7 ^ (2 * n_n.succ + 1) + 3 ^ (2 * n_n.succ + 1) = 4 * (10*7^(2*n_n+1)) + 9 * (7^(2*n_n+1)+3^(2*n_n+1)),
{calc 7 ^ (2 * n_n.succ + 1) + 3 ^ (2 * n_n.succ + 1) 
     = 7 ^ (2 * n_n + 3) + 3 ^ (2 * n_n + 3) : by {ring}
...  = 49 * 7 ^ (2 * n_n + 1) + 9 * 3 ^ (2 * n_n + 1) :
     begin
          have lem : 7 ^ (2 * n_n + 3) = 49 * 7 ^ (2 * n_n + 1),
          {rw pow_succ, rw pow_succ, ring},
          rw lem,
          have lem : 3 ^ (2 * n_n + 3) = 9 * 3 ^ (2 * n_n + 1),
          {rw pow_succ, rw pow_succ, ring},
          rw lem,
     end
...  = 40 * 7 ^ (2 * n_n + 1) + 9 * 7 ^ (2 * n_n + 1) + 9 *  3 ^ (2 * n_n + 1) : by {ring}
...  = 40 * 7 ^ (2 * n_n + 1) + 9 * (7 ^ (2 * n_n + 1) + 3 ^ (2 * n_n + 1)) : by {ring}
...  = 4 * (10*7^(2*n_n+1)) + 9 * (7^(2*n_n+1)+3^(2*n_n+1)) : by {ring},
},
rw lem,
refine has_dvd.dvd.linear_comb _ n_ih 4 9,
exact dvd_mul_right 10 (7 ^(2*n_n+1)),
end


theorem warmup : ∀ n : ℕ , 7^n ≡ 3^n [MOD 4] :=
begin
intros,
exact nat.modeq.pow n 
     begin 
          refl 
     end,
end

theorem hatvanyok_2 : ∀ n : ℕ , 7^(2*n+1) + 3^(2*n+1) ≡ 0 [MOD 10] :=
begin
intros,
rw pow_add,
rw pow_add,
norm_num,
rw pow_mul,
rw pow_mul,
norm_num,
     have H1 : (49^n ≡ 9^n [MOD 10]) := 
     begin
          exact nat.modeq.pow n rfl,
     end,
     have H2 : (49 ^ n * 7 ≡ 9 ^ n * 7 [MOD 10]) :=
     begin
          exact nat.modeq.mul H1 rfl,
     end,
     have H3 : (49 ^ n * 7 + 9 ^ n * 3 ≡ 9 ^ n * 7 + 9 ^ n * 3 [MOD 10]) 
     := 
     begin
          exact nat.modeq.add_right (9 ^ n * 3) H2,
     end,
     have H4 : (9 ^ n * 7 + 9 ^ n * 3 ≡ 0 [MOD 10]) :=
     begin
          ring_nf, refine nat.modeq_zero_iff_dvd.mpr _,
          exact dvd.intro (9 ^ n) rfl,
     end,
     exact nat.modeq.trans H3 H4,
end