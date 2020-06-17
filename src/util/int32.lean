import data.zmod.basic order.basic

def int32 := zmod (2^32)

namespace int32

local attribute [instance]
def int32_pos : fact (0 < 2 ^ 32) := nat.pow_pos dec_trivial _

instance : has_coe int32 ℤ :=
⟨λ i, if i.val < 2^31 then i.val else i.val - 2^32⟩

instance : comm_ring int32 := by unfold int32; apply_instance

instance : decidable_eq int32 :=
λ x y, decidable_of_iff _ (zmod.val_injective _).eq_iff

theorem coe_inj {i j : int32} : (i : ℤ) = j ↔ i = j :=
⟨λ h : (ite (i.val < 2 ^ 31) i.val (i.val - 2 ^ 32) : ℤ) =
       ite (j.val < 2 ^ 31) j.val (j.val - 2 ^ 32), begin
  rw ← (_ : ((2 ^ 32 : ℕ) : ℤ) = 2 ^ 32) at h,
  swap, {apply int.coe_nat_pow},
  split_ifs at h with h₁ h₂,
  { exact zmod.val_injective _ (int.coe_nat_inj h) },
  { have := int.coe_nat_nonneg i.val,
    rw [h, sub_nonneg, int.coe_nat_le] at this,
    cases not_lt_of_le this j.val_lt },
  { have := int.coe_nat_nonneg j.val,
    rw [← h, sub_nonneg, int.coe_nat_le] at this,
    cases not_lt_of_le this i.val_lt },
  { rw sub_left_inj at h,
    exact zmod.val_injective _ (int.coe_nat_inj h) }
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
