module Bottom.Bottom where

open import Level renaming (suc to lsuc ; zero to lzero)
open import Function.Base
import Function

open import Relation.Nullary
open import Data.List.Relation.Unary.Sorted.TotalOrder using (Sorted)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq

open import Data.Nat as ℕ using (ℕ ; suc ; zero ; _<_ ; pred)
import Data.Nat.Properties as ℕ
open import Data.Nat.Induction
open import Data.List as List using (_∷_ ; [] ; List ; sum )
open import Data.List.Relation.Unary.Linked using ([-] ; [] ; _∷_)
open import Data.List.Relation.Unary.All as All using (All ; _∷_ ; [])
open import Data.List.NonEmpty as List⁺ using (List⁺ ; _∷_)
open import Data.Product using (∃ ; _,_)
open import Data.String as String using (String)
open import Data.Char as Char using (Char)

open import Bottom.Foreign.Haskell

private
  variable
    ℓ ℓ' : Level
    A B C : Set ℓ
    n m : ℕ


module _ (b₀ : ℕ) (P : ℕ → Set ℓ) (base : ∀ n → n < suc b₀ → P n) (step : ∀ n → P n → P (suc b₀ ℕ.+ n)) where

  private
    b = b₀

  wfStep : (n : ℕ) → (∀ m → m < n → P m) → P n
  wfStep n rec with ℕ.compare n b
  ... | ℕ.less .n k = base n (ℕ.s≤s (ℕ.≤-step (ℕ.m≤m+n n k)))
  ... | ℕ.equal .n = base n ℕ.≤-refl
  ... | ℕ.greater .b₀ k = step k (rec k (ℕ.s≤s (ℕ.m≤n+m k b₀)))

  +induction : ∀ x → P x
  +induction = <-rec P wfStep


data Emoji : Set where
  comma beg sparkle glitterheart hug heart : Emoji

value : Emoji → ℕ
value hug = 200
value glitterheart = 50
value sparkle = 10
value beg = 5
value comma = 1
value heart = 0

character : Emoji → String
character comma = "\x002C"
character beg = "\x1F97A"
character sparkle = "\x2728"
character glitterheart = "\x1F496"
character hug = "\x1FAC2"
character heart = "\x2764\xFE0F"

separator : String
separator = "\x1F449\x1F448"

fromValue : ℕ → Emoji
fromValue n with n ℕ.≟ 200
... | yes _ = hug
... | no _ with n ℕ.≟ 50
... | yes _ = glitterheart
... | no _ with n ℕ.≟ 10
... | yes _ = sparkle
... | no _ with n ℕ.≟ 5
... | yes _ = beg
... | no _ with n ℕ.≟ 1
... | yes _ = comma
... | no _ = heart


Injective : (A → B) → Set _
Injective = Function.Injective _≡_ _≡_

Inverseˡ : (A → B) → (B → A) → Set _
Inverseˡ {A = A} {B = B} f g = Function.Inverseˡ {A = A} _≡_ _≡_ f g

Inverseʳ : (A → B) → (B → A) → Set _
Inverseʳ {A = A} {B = B} f g = Function.Inverseʳ {B = B} _≡_ _≡_ f g

invʳ→inj : {f : A → B} (g : B → A) → Inverseʳ f g → Injective f
invʳ→inj {f = f} g p {x} {y} q =
  x ≡⟨ sym (p x) ⟩
  g (f x) ≡⟨ cong g q ⟩
  g (f y) ≡⟨ p y ⟩
  y ∎ where open ≡-Reasoning

fromValue-value : Inverseʳ value fromValue
fromValue-value heart = refl
fromValue-value comma = refl
fromValue-value beg = refl
fromValue-value sparkle = refl
fromValue-value glitterheart = refl
fromValue-value hug = refl

value-injective : ∀ {x y} → value x ≡ value y → x ≡ y
value-injective = invʳ→inj fromValue fromValue-value

_≟_ : (x y : Emoji) → Dec (x ≡ y)
x ≟ y with value x ℕ.≟ value y
... | yes p = yes (value-injective p)
... | no ¬p = no (λ p → ¬p (cong value p))

_≤_ : Emoji → Emoji → Set
_≤_ = ℕ._≤_ on value


≤-antisym : Antisymmetric _≡_ (ℕ._≥_ on value)
≤-antisym lt gt = value-injective (ℕ.≤-antisym gt lt)

isTotalOrder : IsTotalOrder _≡_ (ℕ._≥_ on value)
isTotalOrder = record
  { isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ { refl → ℕ.≤-refl }
      ; trans = flip ℕ.≤-trans
      }
    ; antisym = ≤-antisym
    }
  ; total = λ _ _ → ℕ.≤-total _ _
  }

isDecTotalOrder : IsDecTotalOrder _≡_ (ℕ._≥_ on value)
isDecTotalOrder = record
  { isTotalOrder = isTotalOrder
  ; _≟_ = _≟_
  ; _≤?_ = λ x y → _ ℕ.≤? _
  }

Emoji-Order : TotalOrder _ _ _
Emoji-Order = record
  { Carrier = Emoji
  ; _≈_ = _≡_
  ; _≤_ = ℕ._≥_ on value
  ; isTotalOrder = isTotalOrder
  }

record Group : Set where
  constructor mkGrp
  field
    emoji⁺ : List⁺ Emoji

  emoji = List⁺.toList emoji⁺

  field

    @0 sorted : Sorted Emoji-Order emoji

_Reps_ : Group → ℕ → Set
_Reps_ g n = sum (List.map value (Group.emoji g)) ≡ n


data Head_≤_ : List Emoji → Emoji → Set where
  nil : ∀ {e} → Head [] ≤ e
  cons : ∀ {e e' es} → e' ≤ e → Head (e' ∷ es) ≤ e

record HasRep_at_ (n : ℕ) (@0 e : Emoji) : Set where
  constructor mkRepAt
  field
    group : Group
    rep : group Reps n
    @0 head≤ : List⁺.head (Group.emoji⁺ group) ≤ e

@0 head≤-weaken : ∀ {xs e e'} → e ≤ e' → Head xs ≤ e → Head xs ≤ e'
head≤-weaken p nil = nil
head≤-weaken p (cons q) = cons (ℕ.≤-trans q p)

Rep-at-weaken : ∀ {n e e'} → (@0 _ : e ≤ e') → HasRep n at e → HasRep n at e'
Rep-at-weaken p (mkRepAt group reps head≤) = mkRepAt group reps (ℕ.≤-trans head≤ p)

toEmoji⁺-at : ∀ e n → (suc (pred (value e)) ≡ value e) → (∀ m → m < value e → HasRep m at e) → HasRep n at e
toEmoji⁺-at e n val-sucpred base = +induction
  (pred (value e))
  (λ n → HasRep n at e)
  (λ n p → base n (subst (n <_) val-sucpred p))
  (λ n p → subst (λ k → HasRep (k ℕ.+ n) at e) (sym val-sucpred) (step n p))
  n
  where
  step : ∀ k → HasRep k at e → HasRep (value e ℕ.+ k) at e
  step k (mkRepAt (mkGrp (e' ∷ []) sorted) sum-≡ head≤) with e' ≟ heart
  ... | yes refl = mkRepAt (mkGrp (e ∷ []) [-]) (cong (value e ℕ.+_) sum-≡) ℕ.≤-refl
  ... | no ¬p = mkRepAt (mkGrp (e ∷ e' ∷ []) (head≤ ∷ sorted)) (cong (value e ℕ.+_) sum-≡) ℕ.≤-refl
  step k (mkRepAt (mkGrp (e' ∷ e'' ∷ es) sorted) sum-≡ head≤) = mkRepAt (mkGrp (e ∷ e' ∷ e'' ∷ es) (head≤ ∷ sorted)) (cong (value e ℕ.+_) sum-≡) ℕ.≤-refl

HasRep : ℕ → Set
HasRep n = ∃ (_Reps n)

toEmoji : ∀ n → ∃ (_Reps n)
toEmoji n = HasRep_at_.group rep , HasRep_at_.rep rep where
  rep : HasRep n at hug
  rep = toEmoji⁺-at hug n refl
    λ m lt → Rep-at-weaken (ℕ.m≤m*n 50 {4} (ℕ.s≤s ℕ.z≤n)) $ toEmoji⁺-at glitterheart m refl
      λ m lt → Rep-at-weaken (ℕ.m≤m*n 10 {5} (ℕ.s≤s ℕ.z≤n)) $ toEmoji⁺-at sparkle m refl
        λ m lt → Rep-at-weaken (ℕ.m≤m*n 5 {2} (ℕ.s≤s ℕ.z≤n)) $ toEmoji⁺-at beg m refl
          λ m lt → Rep-at-weaken (ℕ.s≤s ℕ.z≤n) $ toEmoji⁺-at comma m refl
            λ { .zero (ℕ.s≤s ℕ.z≤n) → Rep-at-weaken ℕ.z≤n (mkRepAt (mkGrp (heart ∷ []) [-]) refl ℕ.z≤n) }

renderBottomByte : HasRep n → String
renderBottomByte (group , sum-≡) = String.concat (List.map character (Group.emoji group)) String.++ separator

encodeBytes : (xs : List Word8) → All HasRep (List.map word8ToNat xs)
encodeBytes xs = All.universal toEmoji _

encodeNats : (xs : List ℕ) → All HasRep xs
encodeNats = All.universal toEmoji

render : ∀ {xs} → All HasRep xs → String
render = String.concat ∘ All.reduce renderBottomByte

test-1 : render (encodeNats (84 ∷ 101 ∷ 115 ∷ 116 ∷ [])) ≡ "💖✨✨✨,,,,👉👈💖💖,👉👈💖💖✨🥺👉👈💖💖✨🥺,👉👈"
test-1 = refl
