
-- import data.array.lemmas
import tactic
import tactic.squeeze
import data.list.basic
-- import tactic.linarith
-- import data.finmap

universes u v w

structure label (α : Type w) (m : Type u → Type v) (β : Type u) :=
(apply : α → m β)

def goto {α β} {m : Type u → Type v} (f : label α m β) (x : α) := f.apply x

class monad_cont (m : Type u → Type v)
extends monad m :=
(call_cc : Π {α β}, ((label α m β) → m α) → m α)

open monad_cont
class is_lawful_monad_cont (m : Type u → Type v) [monad_cont m]
extends is_lawful_monad m :=
(call_cc_bind_right {α ω γ} (cmd : m α) (next : (label ω m γ) → α → m ω) :
  call_cc (λ f, cmd >>= next f) = cmd >>= λ x, call_cc (λ f, next f x))
(call_cc_bind_left {α} (β) (x : α) (dead : label α m β → β → m α) :
  call_cc (λ f : label α m β, goto f x >>= dead f) = pure x)
(call_cc_dummy {α β} (dummy : m α) :
  call_cc (λ f : label α m β, dummy) = dummy)

export is_lawful_monad_cont

def cont_t (r : Type u) (m : Type u → Type v) (α : Type w) := (α → m r) → m r

namespace cont_t

variables {r : Type u} {m : Type u → Type v} {α β γ ω : Type w}

def run : cont_t r m α → (α → m r) → m r := id

def map (f : m r → m r) (x : cont_t r m α) : cont_t r m α := f ∘ x

lemma run_cont_t_map_cont_t (f : m r → m r) (x : cont_t r m α) :
  run (map f x) = f ∘ run x := rfl

def with_cont_t (f : (β → m r) → α → m r) (x : cont_t r m α) : cont_t r m β :=
λ g, x $ f g

lemma run_with_cont_t (f : (β → m r) → α → m r) (x : cont_t r m α) :
  run (with_cont_t f x) = run x ∘ f := rfl

-- def call_cc (f : (α → cont_t r m β) → cont_t r m α) : cont_t r m α :=
-- λ g, f (λ x h, g x) g

instance : monad (cont_t r m) :=
{ pure := λ α x f, f x,
  bind := λ α β x f g, x $ λ i, f i g }

-- variables [is_lawful_monad m]

instance : is_lawful_monad (cont_t r m) :=
{ id_map := by { intros, refl },
  pure_bind := by { intros, ext, refl },
  bind_assoc := by { intros, ext, refl } }

instance [monad m] : has_monad_lift m (cont_t r m) :=
{ monad_lift := λ a x f, x >>= f }

lemma monad_lift_bind [monad m] [is_lawful_monad m] {α β} (x : m α) (f : α → m β) :
  (monad_lift (x >>= f) : cont_t r m β) = monad_lift x >>= monad_lift ∘ f :=
by { ext, simp only [monad_lift,has_monad_lift.monad_lift,(∘),(>>=),bind_assoc,id.def] }

instance : monad_cont (cont_t r m) :=
{ call_cc := λ α β f g, f ⟨λ x h, g x⟩ g }

instance : is_lawful_monad_cont (cont_t r m) :=
{ call_cc_bind_right := by intros; ext; refl,
  call_cc_bind_left := by intros; ext; refl,
  call_cc_dummy := by intros; ext; refl }

end cont_t

section take_while
open list (hiding take_while)
variables {r : Type u} {m : Type u → Type v} {α β γ ω : Type w}

def take_while' [monad_cont m] {α} (p : α → Prop) [decidable_pred p] (xs : list α) : m (list α) :=
call_cc $ λ leave,
do rs ← mfoldl (λ rs x,
               if p x then pure $ x :: rs
               else goto leave rs.reverse )
               [] xs,
   pure rs.reverse

def take_while (p : α → Prop) [decidable_pred p] (xs : list α) : list α :=
cont_t.run (take_while' p xs) id

meta def assigned : tactic unit :=
do tactic.cleanup

lemma take_while_eq' [monad_cont m] [is_lawful_monad_cont m] {α} (p : α → Prop) [decidable_pred p] (xs : list α) :
  take_while' p xs = (pure $ list.take_while p xs : m (list α)) :=
begin
  suffices : take_while' p xs = (pure $ [].reverse ++ list.take_while p xs : m (list α)),
  { revert this, simp only [imp_self, list.nil_append, list.reverse_nil] },
  dunfold take_while', generalize : list.nil = rs,
  induction xs with x xs generalizing rs,
  { simp only [list.take_while, call_cc_dummy, mfoldl, list.append_nil, pure_bind], },
  { simp [list.take_while, list.mfoldl_cons], split_ifs,
    { simp only [xs_ih,reverse_cons,cons_append,eq_self_iff_true,nil_append,pure_bind,append_assoc] },
    { simp only [bind_assoc, list.append_nil, call_cc_bind_left] } },
end

lemma take_while_eq (p : α → Prop) [decidable_pred p] (xs : list α) :
  take_while p xs = list.take_while p xs :=
by rw [take_while,take_while_eq']; refl

end take_while

section duff -- not the beer

open nat
variables {m : Type u → Type v} {α β γ ω : Type u}
variables (f : α → m α)

section iter
variables [monad m]
def iterate' : ℕ → α → m α
| 0 := pure
| (succ n) := λ x, f x >>= iterate' n
open list

lemma iterate_eq_foldl (n : ℕ) (x : α) :
  iterate' f n x = mfoldl (λ i _, f i)  x (iota n) :=
begin
  induction n with n generalizing x, refl,
  dsimp [iterate',mfoldl,iota],
  congr, ext, apply n_ih,
end

variables [is_lawful_monad m]

lemma iterate_succ' (n : ℕ) (x : α) :
  iterate' f (succ n) x = iterate' f n x >>= f :=
begin
  dsimp [iterate'],
  induction n with n generalizing x;
  simp only [iterate', *, bind_pure, nat.nat_zero_eq_zero, pure_bind],
  rw [← bind_assoc,n_ih],
end

lemma iterate_succ'' (n : ℕ) :
  iterate' f (succ n) = λ x, iterate' f n x >>= f :=
by ext; rw _root_.iterate_succ'

lemma iterate_bind_iterate (x : α) (n k : ℕ) :
  iterate' f k x >>= iterate' f n = iterate' f (k + n) x :=
by induction k generalizing x; simp only [iterate',*,bind_assoc,pure_bind,zero_add,succ_add]

lemma iterate_iterate (n k : ℕ) :
  iterate' (iterate' f n) k = iterate' f (n*k) :=
by induction k; simp only [iterate',*,iterate_bind_iterate,mul_succ,mul_zero,eq_self_iff_true,add_comm]

end iter

variables [monad_cont m]

def iterate_duff' : Π n, (array n (label α m α) → α → m α) → α → m α
| 0 f x := f array.nil x
| (succ n) g x :=
call_cc $ λ goto_n,
do y ← iterate_duff' n (λ a, g $ a.push_back goto_n) x,
   f y

def duff_idx {n} : fin n → fin n
| ⟨i,hi⟩ :=
have h : n - (i + 1) < n,
  from nat.sub_lt_self (lt_of_le_of_lt (nat.zero_le _) hi) (zero_lt_succ _),
⟨n - (i+1), h⟩

def iterate_duff {n} (i : fin n) : α → m α :=
iterate_duff' f n $ λ a,
goto (a.read (duff_idx i))

variables [is_lawful_monad_cont m]

@[simp]
lemma iterate_duff_dummy (n : ℕ) (goto_n : α → m α) (x : α) :
  iterate_duff' f n (λ (a : array n (label α m α)), goto_n) x = goto_n x >>= iterate' f n :=
begin
  induction n generalizing goto_n;
  simp only [iterate_duff',*,_root_.iterate_succ'',call_cc_dummy,bind_assoc],
  simp only [iterate', bind_pure],
end

lemma read_push_back {n} (a : array n α) (x : α) (i : fin $ n+1) :
  (a.push_back x).read (duff_idx i) =
  if h' : i = 0 then x
  else a.read (duff_idx $ i.pred h') :=
by { cases i, dsimp [array.push_back,array.read,duff_idx,d_array.read],
     apply dif_ctx_congr, intros, refl,
     { intros, dsimp [duff_idx,fin.pred], congr' 2,
       cases i_val, contradiction,
       dsimp [pred], rw nat.add_sub_add_right, },
     { rw [nat.add_sub_add_right,nat.sub_eq_iff_eq_add],
       conv { to_lhs, to_lhs, rw ← add_zero n },
       rw add_left_inj, split; intro h;
       try { injection h }; subst i_val; refl,
       apply le_of_lt_succ i_is_lt, } }

lemma coe_pred {n} (i : fin $ succ n) (h : i ≠ 0) :
  ↑(i.pred h) = nat.pred i :=
by cases i; refl

lemma iterate_duff_def {n} (i : fin n) (x : α) :
  iterate_duff f i x = iterate' f i x :=
begin
  dsimp [iterate_duff],
  induction n generalizing i,
  { cases not_lt_zero _ i.is_lt },
  { simp only [iterate_duff', read_push_back], split_ifs,
    { subst i,
      unfold_coes, unfold has_zero.zero,
      simp only [iterate',call_cc_bind_left,bind_assoc, iterate_duff_dummy] },
    { specialize n_ih (i.pred h), simp only [n_ih, call_cc_dummy, coe_pred],
      cases i with i, cases i, contradiction,
      unfold_coes, dsimp [fin.val],
      rw [_root_.iterate_succ'] } }
end

def push_each : Π (l : list α) {n}, array n α → array (n + l.length) α
| [] n a := a
| (x :: xs) n a :=
have n + 1 + xs.length = (n + list.length (x :: xs)),
  by simp only [list.length, add_comm, add_left_comm],
cast (by rw this) $ push_each xs $ a.push_back x

lemma iterate_duff_def_4 (i : fin 4) (x : α) :
  iterate' f i x =
  call_cc (λ goto_n_0 : label α m α,
  call_cc (λ goto_n_1,
  call_cc (λ goto_n_2,
  call_cc (λ goto_n_3,
    let a := push_each [goto_n_3,goto_n_2,goto_n_1,goto_n_0] array.nil in
    goto (a.read (duff_idx i)) x >>=
  λ (y₄ : α), f y₄) >>=
  λ (y₃ : α), f y₃) >>=
  λ (y₂ : α), f y₂) >>=
  λ (y₁ : α), f y₁)
 :=
begin
  rw ← iterate_duff_def,
  dsimp [iterate_duff,iterate_duff'], refl,
end

lemma unroll_iterate_def (n c : ℕ) (h : n > 0) (x : α) :
  iterate' f c x =
  iterate_duff f ⟨c % n, mod_lt c h ⟩ x >>=
  iterate' (iterate' f n) (c / n)  :=
begin
  rw iterate_duff_def, unfold_coes, dsimp [fin.val],
  simp only [iterate_iterate,iterate_bind_iterate,mod_add_div],
end

lemma unroll_iterate_def_4 (c : ℕ) (x : α) :
  iterate' f c x =
  call_cc (λ goto_n_0 : label α m α,
  call_cc (λ goto_n_1,
  call_cc (λ goto_n_2,
  call_cc (λ goto_n_3,
    let a := push_each [goto_n_3,goto_n_2,goto_n_1,goto_n_0] array.nil in
    goto (a.read $ duff_idx (⟨c % 4,mod_lt c dec_trivial⟩)) x >>=
  λ (y₄ : α), f y₄) >>=
  λ (y₃ : α), f y₃) >>=
  λ (y₂ : α), f y₂) >>=
  λ (y₁ : α), f y₁) >>=
  iterate' (λ x,
    f x >>= f >>=
    f >>= f)
    (c / 4) :=
begin
  rw unroll_iterate_def _ 4,
  dsimp [iterate_duff,iterate',iterate_duff'],
  congr, ext, simp only [bind_assoc,bind_pure], apply_instance
end

end duff
