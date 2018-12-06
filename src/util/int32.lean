import data.zmod.basic order.basic

def int32 := zmod ⟨2^32, nat.pow_pos dec_trivial _⟩

namespace int32

instance : has_coe int32 ℤ :=
⟨λ i, if i.1 < 2^31 then i.1 else i.1 - 2^32⟩

instance : comm_ring int32 := by unfold int32; apply_instance

instance : decidable_eq int32 :=
λ x y, decidable_of_iff' _ (fin.eq_iff_veq _ _)

theorem coe_inj {i j : int32} : (i : ℤ) = j ↔ i = j :=
⟨λ h : (ite (i.1 < 2 ^ 31) i.1 (i.1 - 2 ^ 32) : ℤ) =
       ite (j.1 < 2 ^ 31) j.1 (j.1 - 2 ^ 32), begin
  rw ← (_ : ((2 ^ 32 : ℕ) : ℤ) = 2 ^ 32) at h,
  swap, {apply int.coe_nat_pow},
  split_ifs at h with h₁ h₂,
  { exact fin.eq_of_veq (int.coe_nat_inj h) },
  { have := int.coe_nat_nonneg i.1,
    rw [h, sub_nonneg, int.coe_nat_le] at this,
    cases not_lt_of_le this j.2 },
  { have := int.coe_nat_nonneg j.1,
    rw [← h, sub_nonneg, int.coe_nat_le] at this,
    cases not_lt_of_le this i.2 },
  { rw sub_right_inj at h,
    exact fin.eq_of_veq (int.coe_nat_inj h) }
end, congr_arg _⟩

instance : decidable_linear_order int32 :=
{ decidable_le := λ x y, int.decidable_le _ _,
  decidable_eq := int32.decidable_eq,
  ..linear_order.lift (coe : int32 → ℤ) (λ _ _, coe_inj.1) }

theorem coe_le {i j : int32} : (i : ℤ) ≤ j ↔ i ≤ j := iff.rfl

theorem coe_lt {i j : int32} : (i : ℤ) < j ↔ i < j :=
by rw [← not_le, coe_le, not_le]

theorem coe_zero : ((0 : int32) : ℤ) = 0 :=
by unfold_coes; exact if_pos (nat.pow_pos dec_trivial _)

def of_int (n : ℤ) : option int32 :=
if -2^31 ≤ n ∧ n < 2^31 then some n else none

def div (m n : int32) : option int32 :=
if n = 0 then none else of_int (m / n)

def mod (m n : int32) : option int32 :=
if n = 0 then none else of_int (m % n)

def shl (m n : int32) : option int32 :=
if 0 ≤ n ∧ n < 32 then of_int (int.shiftl m n) else none

def shr (m n : int32) : option int32 :=
if 0 ≤ n ∧ n < 32 then of_int (int.shiftr m n) else none

def bitwise_and (m n : int32) : int32 := int.land m n
def bitwise_xor (m n : int32) : int32 := int.lxor m n
def bitwise_or (m n : int32) : int32 := int.lor m n
def bitwise_not (n : int32) : int32 := int.lnot n

end int32
