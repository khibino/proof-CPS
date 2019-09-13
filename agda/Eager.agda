module Eager where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
import Relation.Binary.PropositionalEquality as E


data Ty : Set where
  ty-nat  : Ty
  ty-bool : Ty
  _⟶_   : Ty → Ty → Ty

{-
eqTy : (x y : Ty) → Dec (x ≡ y)
eqTy ty-nat ty-bool     =  no (λ ())
eqTy ty-bool ty-nat     =  no (λ ())
eqTy ty-nat (_ ⟶ _)   =  no (λ ())
eqTy (_ ⟶ _) ty-nat   =  no (λ ())
eqTy ty-bool (_ ⟶ _)  =  no (λ ())
eqTy (_ ⟶ _) ty-bool  =  no (λ ())
eqTy ty-nat ty-nat      =  yes refl
eqTy ty-bool ty-bool    =  yes refl
eqTy (x₁ ⟶ x₂) (y₁ ⟶ y₂) with eqTy x₁ y₁ | eqTy x₂ y₂
... | yes e₁ | yes e₂   =  yes (E.cong₂ _⟶_ e₁ e₂)
... | yes e₁ | no ¬e₂   =  no (λ { refl → ¬e₂ refl })
... | no ¬e₁ | _        =  no (λ { refl → ¬e₁ refl })
 -}

id : Set
id = ℕ

-- tm

data tm : Set where
  tm-nat  : ℕ → tm
  tm-bool : Bool → tm
  tm-var  : id → tm
  tm-abs  : id → Ty → tm → tm
  tm-app  : tm → tm → tm
  tm-if   : tm → tm → tm → tm

subst-syntax : tm → id → tm → tm
subst-syntax v x = subst
  where
    subst : tm → tm
    subst (tm-nat v)       = tm-nat v
    subst (tm-bool b)      = tm-bool b
    subst (tm-var x₁) with x₁ ≟ x
    ...  | yes p           = v
    ...  | no ¬p           = tm-var x₁
    subst (tm-abs x₁ T t) with x₁ ≟ x
    ...  | yes p           = tm-abs x₁ T t
    ...  | no ¬p           = tm-abs x₁ T (subst t)
    subst (tm-app t₁ t₂)   = tm-app (subst t₁) (subst t₂)
    subst (tm-if t₁ t₂ t₃) = tm-if (subst t₁) (subst t₂) (subst t₃)

syntax subst-syntax v x = ⟦ v / x ⟧

data value : tm → Set where
  v-nat  : (n : ℕ) → value (tm-nat n)
  v-bool : (b : Bool) → value (tm-bool b)
  v-abs  : (vn : id) → (T : Ty) → (body : tm) → value (tm-abs vn T body)

data _⟹_ : tm → tm → Set where
  st-abs  : ∀ v x t T →
            value v        →   -- eager
            tm-app (tm-abs x T t) v ⟹ ⟦ v / x ⟧ t
  st-app₁ : ∀ t₁ t₁' t₂ →
            t₁ ⟹ t₁'       →
            tm-app t₁ t₂ ⟹ tm-app t₁' t₂
  st-app₂ : ∀ t₁ t₂ t₂' →
            t₂ ⟹ t₂'       →
            tm-app t₁ t₂ ⟹ tm-app t₁ t₂'
  st-then : ∀ t₂ t₃ →
            tm-if (tm-bool true)  t₂ t₃ ⟹ t₂
  st-else : ∀ t₂ t₃ →
            tm-if (tm-bool false) t₂ t₃ ⟹ t₃
  st-if   : ∀ t₁ t₁' t₂ t₃ →
            t₁ ⟹ t₁'          →
            tm-if t₁ t₂ t₃ ⟹ tm-if t₁' t₂ t₃

-- partial-map type
pm : Set → Set
pm A = id → Maybe A

empty : ∀ {A} → pm A
empty  _ = nothing

-- extend
extend : ∀ {A} → pm A → id → A → pm A
extend Γ x T y with y ≟ x
...  | yes _ = just T
...  | no  _ = Γ y

extend-eq :
  {A : Set} →
  (Γ : pm A) → (x : id) → (T : A) →
  extend Γ x T x ≡ just T
extend-eq Γ x T with x ≟ x
extend-eq Γ x T | yes _ = refl
extend-eq Γ _ T | no n  = ⊥-elim (n refl)

extend-neq :
  {A : Set} →
  (Γ : pm A) → (x : id) → (T : A) →
  (y : id) →
   y ≢ x    →
  extend Γ x T y ≡ Γ y
extend-neq Γ x T y ne with y ≟ x
... | yes p = ⊥-elim (ne p)
... | no _  = refl

-- has-type
data _⊢_∶_ : pm Ty → tm → Ty → Set where
  ht-nat   : ∀ Γ n →
             Γ ⊢ tm-nat n ∶ ty-nat
  ht-bool  : ∀ Γ b →
             Γ ⊢ tm-bool b ∶ ty-bool
  ht-var   : ∀ Γ x T →
              Γ x ≡ just T →
              Γ ⊢ tm-var x ∶ T
  ht-abs   : ∀ Γ x U T t →
             extend Γ x U ⊢ t ∶ T →
             Γ ⊢ tm-abs x U t ∶ (U ⟶ T)
  ht-app   : ∀ Γ S T t₁ t₂ →
             Γ ⊢ t₁  ∶ (S ⟶ T) →
             Γ ⊢ t₂  ∶ S           →
             Γ ⊢ tm-app t₁ t₂ ∶ T
  ht-if    : ∀ Γ T t₁ t₂ t₃ →
             Γ ⊢ t₁ ∶ ty-bool    →
             Γ ⊢ t₂ ∶ T          →
             Γ ⊢ t₃ ∶ T          →
             Γ ⊢ tm-if t₁ t₂ t₃ ∶ T

var-a : ℕ
var-a = 0

typing-example-1 :
  empty ⊢ (tm-abs var-a ty-bool (tm-var var-a)) ∶ (ty-bool ⟶ ty-bool)
typing-example-1 =
  ht-abs empty var-a ty-bool ty-bool (tm-var var-a)
  (ht-var (extend empty var-a ty-bool) var-a ty-bool (extend-eq empty var-a ty-bool))

data appears-free-in : id → tm → Set where
  afi-var  : ∀ x →
             appears-free-in x (tm-var x)
  afi-app₁ : ∀ x t₁ t₂ →
             appears-free-in x t₁ →
             appears-free-in x (tm-app t₁ t₂)
  afi-app₂ : ∀ x t₁ t₂ →
             appears-free-in x t₂ →
             appears-free-in x (tm-app t₁ t₂)
  afi-abs  : ∀ x y T₁₁ t₁₂ →
             x ≢ y →
             appears-free-in x t₁₂ →
             appears-free-in x (tm-abs y T₁₁ t₁₂)
  afi-if   : ∀ x t₁ t₂ t₃ →
             appears-free-in x t₁ →
             appears-free-in x (tm-if t₁ t₂ t₃)
  afi-then : ∀ x t₁ t₂ t₃ →
             appears-free-in x t₂ →
             appears-free-in x (tm-if t₁ t₂ t₃)
  afi-else : ∀ x t₁ t₂ t₃ →
             appears-free-in x t₃ →
             appears-free-in x (tm-if t₁ t₂ t₃)

closed : tm → Set
closed t = ∀ x → ¬ appears-free-in x t

free-in-context : ∀ x t T Γ     →
                  appears-free-in x t →
                  Γ ⊢ t ∶ T          →
                  (∃[ T' ] (Γ x ≡ just T'))
free-in-context x .(tm-var x)       T           Γ (afi-var .x)              (ht-var .Γ .x .T e)
  =  T , e
free-in-context x .(tm-app t₁ t₂)   T           Γ (afi-app₁ .x t₁ t₂ fi)    (ht-app .Γ T₁₁ .T .t₁ .t₂ htₐ ht₂)
  =  free-in-context x t₁  (T₁₁ ⟶ T) Γ fi htₐ
free-in-context x .(tm-app t₁ t₂)   T           Γ (afi-app₂ .x t₁ t₂ fi)    (ht-app .Γ T₁₁ .T .t₁ .t₂ htₐ ht₂)
  =  free-in-context x t₂  T₁₁         Γ fi ht₂
free-in-context x .(tm-abs y S t)    .(S ⟶ T) Γ (afi-abs .x y S t ¬eq fi) (ht-abs .Γ .y .S T .t ht) rewrite E.sym (extend-neq Γ y S x ¬eq)
  =  free-in-context x t T             (extend Γ y S) fi ht
free-in-context x .(tm-if t₁ t₂ t₃) T           Γ (afi-if .x t₁ t₂ t₃ fi)   (ht-if .Γ .T .t₁ .t₂ .t₃ ht₁ ht₂ ht₃)
  =  free-in-context x t₁  ty-bool     Γ fi ht₁
free-in-context x .(tm-if t₁ t₂ t₃) T           Γ (afi-then .x t₁ t₂ t₃ fi) (ht-if .Γ .T .t₁ .t₂ .t₃ ht₁ ht₂ ht₃)
  =  free-in-context x t₂  T           Γ fi ht₂
free-in-context x .(tm-if t₁ t₂ t₃) T           Γ (afi-else .x t₁ t₂ t₃ fi) (ht-if .Γ .T .t₁ .t₂ .t₃ ht₁ ht₂ ht₃)
  =  free-in-context x t₃  T           Γ fi ht₃

-- corollary
typable-empty-closed :
  ∀ t T    →
  empty ⊢ t ∶ T →
  closed t
typable-empty-closed t T ht x afi with free-in-context x t T empty afi ht
typable-empty-closed t T ht x afi | _ , ()  --- nothing ≡ just _

context-invariance :
  ∀ Γ₁ Γ₂ t T →
  Γ₁ ⊢ t ∶ T →
  (∀ x → appears-free-in x t → Γ₁ x ≡ Γ₂ x) →
  Γ₂ ⊢ t ∶ T
context-invariance Γ₁ Γ₂ .(tm-nat n)  .ty-nat  (ht-nat .Γ₁ n)      _            = ht-nat  Γ₂ n
context-invariance Γ₁ Γ₂ .(tm-bool b) .ty-bool (ht-bool .Γ₁ b)     _            = ht-bool Γ₂ b
context-invariance Γ₁ Γ₂ .(tm-var x)  T        (ht-var .Γ₁ x .T e) nfe
  rewrite (nfe x (afi-var x)) = ht-var  Γ₂ x T e
context-invariance Γ₁ Γ₂ .(tm-abs x U t) .(U ⟶ T) (ht-abs .Γ₁ x U T t ht) nfe =
  ht-abs Γ₂ x U T t
    (context-invariance (extend Γ₁ x U) (extend Γ₂ x U) t T ht ihfe)
  where
    ihfe : (y : id) → appears-free-in y t → extend Γ₁ x U y ≡ extend Γ₂ x U y
    ihfe y yafi with y ≟ x
    ... | yes p = refl
    ... | no ¬p = nfe y (afi-abs y x U t ¬p yafi)
context-invariance Γ₁ Γ₂ .(tm-app t₁ t₂) T (ht-app .Γ₁ S .T t₁ t₂ ht ht₁) nfe   =
  ht-app Γ₂ S T t₁ t₂
    (context-invariance Γ₁ Γ₂ t₁ (S ⟶ T) ht (λ x z → nfe x (afi-app₁ x t₁ t₂ z)))
    (context-invariance Γ₁ Γ₂ t₂ S ht₁ (λ x z → nfe x (afi-app₂ x t₁ t₂ z)))
context-invariance Γ₁ Γ₂ .(tm-if t₁ t₂ t₃) T (ht-if .Γ₁ .T t₁ t₂ t₃ ht ht₁ ht₂) nfe =
  ht-if Γ₂ T t₁ t₂ t₃
    (context-invariance Γ₁ Γ₂ t₁ ty-bool ht
    (λ x z → nfe x (afi-if x t₁ t₂ t₃ z)))
    (context-invariance Γ₁ Γ₂ t₂ T ht₁
    (λ x z → nfe x (afi-then x t₁ t₂ t₃ z)))
    (context-invariance Γ₁ Γ₂ t₃ T ht₂
    (λ x z → nfe x (afi-else x t₁ t₂ t₃ z)))

substitution-preserves-typing :
  ∀ Γ x U v t T →
  extend Γ x U ⊢ t ∶ T →
  empty ⊢ v ∶ U →
  Γ ⊢ ⟦ v / x ⟧ t ∶ T
substitution-preserves-typing Γ x U v =
    preserve Γ
  where
    subst-var-eq : ⟦ v / x ⟧ (tm-var x) ≡ v
    subst-var-eq with x ≟ x
    ...             | yes eq = refl
    ...             | no ¬eq with ¬eq refl
    ...                         | ()

    subst-var-neq : ∀ x₁ → x₁ ≢ x →  ⟦ v / x ⟧ (tm-var x₁) ≡ (tm-var x₁)
    subst-var-neq x₁ ¬eq with x₁ ≟ x
    ...                     | no ¬p = refl
    ...                     | yes p with ¬eq p
    ...                                | ()

    subst-abs-same : ∀ U₁ t → ⟦ v / x ⟧ (tm-abs x U₁ t) ≡ (tm-abs x U₁ t)
    subst-abs-same U₁ t with x ≟ x
    ...                    | yes eq = refl
    ...                    | no ¬eq with ¬eq refl
    ...                                | ()

    subst-abs-eq : ∀ x₁ U₁ t → x₁ ≡ x → ⟦ v / x ⟧ (tm-abs x₁ U₁ t) ≡ (tm-abs x₁ U₁ t)
    subst-abs-eq x₁ U₁ t eq rewrite eq = subst-abs-same U₁ t

    subst-abs-neq : ∀ x₁ U₁ t → x₁ ≢ x → ⟦ v / x ⟧ (tm-abs x₁ U₁ t) ≡ (tm-abs x₁ U₁ (⟦ v / x ⟧ t))
    subst-abs-neq x₁ U₁ t ¬eq with x₁ ≟ x
    ...                          | no ¬p = refl
    ...                          | yes p with ¬eq p
    ...                                     | ()

    preserve :
      ∀ Γ t T →
      extend Γ x U ⊢ t ∶ T →
      empty ⊢ v ∶ U →
      Γ ⊢ ⟦ v / x ⟧ t ∶ T
    preserve Γ .(tm-nat n)       .ty-nat     (ht-nat _ n)            Hv = ht-nat Γ n
    preserve Γ .(tm-bool b)      .ty-bool    (ht-bool _ b)           Hv = ht-bool Γ b
    preserve Γ .(tm-var x₁)      .T          (ht-var _ x₁ T mx)      Hv
      with x₁ ≟ x
    ...  | yes eq
      rewrite just-injective mx | eq | subst-var-eq =
        context-invariance empty Γ v T Hv vclose
      where
        vclose : ∀ x₂ → appears-free-in x₂ v → empty x₂ ≡ Γ x₂
        vclose x₂ contra with free-in-context x₂ v T empty contra Hv
        vclose x₂ contra    | T₂ , ()
    ...  | no ¬eq
      rewrite extend-neq Γ x U x₁ ¬eq | subst-var-neq x₁ ¬eq =
        ht-var Γ x₁ T mx
    preserve Γ .(tm-abs x₁ U₁ t) .(U₁ ⟶ T) (ht-abs _ x₁ U₁ T t Ht) Hv
      with x₁ ≟ x
    ...  | yes eq
      rewrite subst-abs-eq x₁ U₁ t eq | eq =
        ht-abs Γ x U₁ T t (context-invariance (extend (extend Γ x U) x U₁) (extend Γ x U₁) t T Ht fvty)
      where
        fvty : ∀ x₂ → appears-free-in x₂ t → extend (extend Γ x U) x U₁ x₂ ≡ extend Γ x U₁ x₂
        fvty x₂ afi with x₂ ≟ x
        ...         | yes p rewrite p | extend-eq (extend Γ x U) x U₁                              = refl
        ...         | no ¬p rewrite extend-neq (extend Γ x U) x U₁ x₂ ¬p | extend-neq Γ x U x₂ ¬p = refl
    ...  | no ¬eq
      rewrite subst-abs-neq x₁ U₁ t ¬eq =
        ht-abs Γ x₁ U₁ T (⟦ v / x ⟧ t)
          (preserve (extend Γ x₁ U₁) t T
            (context-invariance (extend (extend Γ x U) x₁ U₁) (extend (extend Γ x₁ U₁) x U) t T Ht fvty)
            Hv)
      where
        fvty : ∀ x₂ → appears-free-in x₂ t → (extend (extend Γ x U) x₁ U₁) x₂ ≡ (extend (extend Γ x₁ U₁) x U) x₂
        fvty x₂ afi with x₂ ≟ x | x₂ ≟ x₁
        fvty x₂ afi | yes e0 | yes e1 with ¬eq (E.trans (E.sym e1) e0)
        ...                              | ()
        fvty x₂ afi | yes e0 | no ¬e1
          rewrite
            extend-neq (extend Γ x U) x₁ U₁ x₂ ¬e1 | e0 | extend-eq Γ x  U  |
            extend-eq (extend Γ x₁ U₁) x U =
              refl
        fvty x₂ afi | no ¬e0 | yes e1
          rewrite
            extend-neq (extend Γ x₁ U₁) x U x₂ ¬e0 | e1 | extend-eq Γ x₁ U₁ |
            extend-eq (extend Γ x U) x₁ U₁ =
              refl
        fvty x₂ afi | no ¬e0 | no ¬e1
          rewrite
            extend-neq (extend Γ x₁ U₁) x U x₂ ¬e0 |
            extend-neq Γ x₁ U₁ x₂ ¬e1 |
            extend-neq (extend Γ x U) x₁ U₁ x₂ ¬e1 |
            extend-neq Γ x U x₂ ¬e0 =
              refl
    preserve Γ .(tm-app t₁ t₂)   .T          (ht-app _ S T t₁ t₂ Ht₁ Ht₂)     Hv
      = ht-app Γ S T (⟦ v / x ⟧ t₁) (⟦ v / x ⟧ t₂)
        (preserve Γ t₁ (S ⟶ T) Ht₁ Hv)
        (preserve Γ t₂  S        Ht₂ Hv)
    preserve Γ .(tm-if t₁ t₂ t₃) .T          (ht-if _ T t₁ t₂ t₃ Ht₁ Ht₂ Ht₃) Hv
      = ht-if Γ T (⟦ v / x ⟧ t₁) (⟦ v / x ⟧ t₂) (⟦ v / x ⟧ t₃)
        (preserve Γ t₁ ty-bool Ht₁ Hv)
        (preserve Γ t₂ T       Ht₂ Hv)
        (preserve Γ t₃ T       Ht₃ Hv)

{-
subst-var-eq : ∀ x v → ⟦ v / x ⟧ (tm-var x) ≡ v
subst-var-eq x _ with x ≟ x
...                 | yes eq = refl
...                 | no ¬eq with ¬eq refl
...                             | ()

subst-var-neq : ∀ x v x₁ → x₁ ≢ x →  ⟦ v / x ⟧ (tm-var x₁) ≡ (tm-var x₁)
subst-var-neq x v x₁ ¬eq
  with x₁ ≟ x
...  | no ¬p = refl
...  | yes p with ¬eq p
...             | ()

subst-abs-same : ∀ v x U₁ t → ⟦ v / x ⟧ (tm-abs x U₁ t) ≡ (tm-abs x U₁ t)
subst-abs-same v x U₁ t
  with x ≟ x
...  | yes eq = refl
...  | no ¬eq with ¬eq refl
...              | ()

subst-abs-eq : ∀ v x x₁ U₁ t → x₁ ≡ x → ⟦ v / x ⟧ (tm-abs x₁ U₁ t) ≡ (tm-abs x₁ U₁ t)
subst-abs-eq v x x₁ U₁ t eq rewrite eq = subst-abs-same v x U₁ t

subst-abs-neq : ∀ v x x₁ U₁ t → x₁ ≢ x → ⟦ v / x ⟧ (tm-abs x₁ U₁ t) ≡ (tm-abs x₁ U₁ (⟦ v / x ⟧ t))
subst-abs-neq v x x₁ U₁ t ¬eq
  with x₁ ≟ x
...  | no ¬p = refl
...  | yes p with ¬eq p
...             | ()

substitution-preserves-typing-x :
  ∀ Γ x U v t T →
  extend Γ x U ⊢ t ∶ T →
  empty ⊢ v ∶ U →
  Γ ⊢ ⟦ v / x ⟧ t ∶ T
substitution-preserves-typing-x Γ x U v .(tm-nat n)       .ty-nat     (ht-nat _ n)                    Hv = ht-nat Γ n
substitution-preserves-typing-x Γ x U v .(tm-bool b)      .ty-bool    (ht-bool _ b)                   Hv = ht-bool Γ b
substitution-preserves-typing-x Γ x U v .(tm-var x₁)      .T          (ht-var _ x₁ T mx)              Hv
  with x₁ ≟ x
...  | yes eq
  rewrite just-injective mx | eq | subst-var-eq x v =
    context-invariance empty Γ v T Hv vclose
  where
    vclose : ∀ x₂ → appears-free-in x₂ v → empty x₂ ≡ Γ x₂
    vclose x₂ contra with free-in-context x₂ v T empty contra Hv
    vclose x₂ contra    | T₂ , ()
...  | no ¬eq
  rewrite extend-neq Γ x U x₁ ¬eq | subst-var-neq x v x₁ ¬eq =
    ht-var Γ x₁ T mx
substitution-preserves-typing-x Γ x U v .(tm-abs x₁ U₁ t) .(U₁ ⟶ T) (ht-abs .(extend Γ x U) x₁ U₁ T t Ht)         Hv
  with x₁ ≟ x
...  | yes eq
  rewrite subst-abs-eq v x x₁ U₁ t eq | eq =
    ht-abs Γ x U₁ T t (context-invariance (extend (extend Γ x U) x U₁) (extend Γ x U₁) t T Ht fvty)
  where
    fvty : ∀ x₂ → appears-free-in x₂ t → extend (extend Γ x U) x U₁ x₂ ≡ extend Γ x U₁ x₂
    fvty x₂ afi with x₂ ≟ x
    ...         | yes p rewrite p | extend-eq (extend Γ x U) x U₁                              = refl
    ...         | no ¬p rewrite extend-neq (extend Γ x U) x U₁ x₂ ¬p | extend-neq Γ x U x₂ ¬p = refl
...  | no ¬eq
  rewrite subst-abs-neq v x x₁ U₁ t ¬eq =
    ht-abs Γ x₁ U₁ T (⟦ v / x ⟧ t)
      (substitution-preserves-typing-x (extend Γ x₁ U₁) x U v t T
         (context-invariance (extend (extend Γ x U) x₁ U₁) (extend (extend Γ x₁ U₁) x U) t T Ht fvty)
         Hv)
  where
    fvty : ∀ x₂ → appears-free-in x₂ t → (extend (extend Γ x U) x₁ U₁) x₂ ≡ (extend (extend Γ x₁ U₁) x U) x₂
    fvty x₂ afi with x₂ ≟ x | x₂ ≟ x₁
    fvty x₂ afi | yes e0 | yes e1 with ¬eq (E.trans (E.sym e1) e0)
    ...                              | ()
    fvty x₂ afi | yes e0 | no ¬e1
      rewrite
        extend-neq (extend Γ x U) x₁ U₁ x₂ ¬e1 | e0 | extend-eq Γ x  U  |
        extend-eq (extend Γ x₁ U₁) x U =
          refl
    fvty x₂ afi | no ¬e0 | yes e1
      rewrite
        extend-neq (extend Γ x₁ U₁) x U x₂ ¬e0 | e1 | extend-eq Γ x₁ U₁ |
        extend-eq (extend Γ x U) x₁ U₁ =
          refl
    fvty x₂ afi | no ¬e0 | no ¬e1
      rewrite
        extend-neq (extend Γ x₁ U₁) x U x₂ ¬e0 |
        extend-neq Γ x₁ U₁ x₂ ¬e1 |
        extend-neq (extend Γ x U) x₁ U₁ x₂ ¬e1 |
        extend-neq Γ x U x₂ ¬e0 =
          refl
substitution-preserves-typing-x Γ x U v .(tm-app t₁ t₂)   .T          (ht-app _ S T t₁ t₂ Ht₁ Ht₂)    Hv =
  ht-app Γ S T (⟦ v / x ⟧ t₁) (⟦ v / x ⟧ t₂)
  (substitution-preserves-typing-x Γ x U v t₁ (S ⟶ T) Ht₁ Hv)
  (substitution-preserves-typing-x Γ x U v t₂  S        Ht₂ Hv)
substitution-preserves-typing-x Γ x U v .(tm-if t₁ t₂ t₃) .T          (ht-if _ T t₁ t₂ t₃ Ht₁ Ht₂ Ht₃) Hv =
  ht-if Γ T (⟦ v / x ⟧ t₁) (⟦ v / x ⟧ t₂) (⟦ v / x ⟧ t₃)
  (substitution-preserves-typing-x Γ x U v t₁ ty-bool Ht₁ Hv)
  (substitution-preserves-typing-x Γ x U v t₂ T       Ht₂ Hv)
  (substitution-preserves-typing-x Γ x U v t₃ T       Ht₃ Hv)
 -}
