import data.nat.basic
import data.nat.pow
import tactic.linarith

theorem hatvanyok : ∀ n : ℕ , 10 ∣ (7^(2*n+1) + 3^(2*n+1)):=
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