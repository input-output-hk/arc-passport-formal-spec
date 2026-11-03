{-# OPTIONS --safe --without-K #-}

-- Raw ABI decoding is fail-closed. No pure export is mistaken for a runtime
-- circuit. Native cryptographic interpretation is the explicit Primitives
-- parameter; successful execution does not itself establish its soundness.
module Conformance.FullAccount where

open import Conformance.FullAccountTypes
open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; _++_; map; length; take; drop)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base hiding (equal)
open import Data.Product.Base hiding (map)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base

-- Foreign scalars and affine coordinates are canonical natural numbers on the
-- wire. Address wrappers are their sole 32-byte member; widths remain in Atoms.
k256ScalarOrder p256ScalarOrder k256BaseOrder p256BaseOrder : ℕ
k256ScalarOrder = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
p256ScalarOrder = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
k256BaseOrder = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
p256BaseOrder = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

data Type : Set where
  natural : ℕ → Type
  boolean : Type
  byteString : ℕ → Type
  product : List Type → Type
  optional : Type → Type
  mapping : Type → Type → Type
  finiteSet : Type → Type
  foreignPoint : Curve → Type

allBytes : Bytes → Bool
allBytes [] = true
allBytes (x ∷ xs) = (x <ᵇ 256) ∧ allBytes xs

unique : List Value → Bool
unique [] = true
unique (x ∷ xs) = not (member x xs) ∧ unique xs

mapKeys : List Value → List Value
mapKeys [] = []
mapKeys (tuple (k ∷ _ ∷ []) ∷ xs) = k ∷ mapKeys xs
mapKeys (_ ∷ xs) = none ∷ mapKeys xs

foreignPointValid : Curve → Value → Bool
foreignPointValid k256 (tuple (nat x ∷ nat y ∷ bool infinity ∷ [])) =
  (x <ᵇ k256BaseOrder) ∧ (y <ᵇ k256BaseOrder) ∧
  (infinity ∨ ((y * y % k256BaseOrder) ≡ᵇ ((x * x * x + 7) % k256BaseOrder)))
foreignPointValid p256 (tuple (nat x ∷ nat y ∷ bool infinity ∷ [])) =
  (x <ᵇ p256BaseOrder) ∧ (y <ᵇ p256BaseOrder) ∧
  (infinity ∨ ((y * y % p256BaseOrder) ≡ᵇ
    ((x * x * x + (p256BaseOrder ∸ 3) * x +
      0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b) % p256BaseOrder)))
foreignPointValid _ _ = false

mutual
  valid : Type → Value → Bool
  valid (natural bound) (nat n) = n <ᵇ bound
  valid boolean (bool _) = true
  valid (byteString n) (bytes bs) = (length bs ≡ᵇ n) ∧ allBytes bs
  valid (product ts) (tuple vs) = validArguments ts vs
  valid (optional t) none = true
  valid (optional t) (some v) = valid t v
  valid (optional t) (tuple (bool _ ∷ v ∷ [])) = valid t v
  valid (mapping k v) (tuple xs) = validEntries k v xs ∧ unique (mapKeys xs)
  valid (finiteSet t) (tuple xs) = validElements t xs ∧ unique xs
  valid (foreignPoint c) v = foreignPointValid c v
  valid _ _ = false

  validArguments : List Type → List Value → Bool
  validArguments [] [] = true
  validArguments (t ∷ ts) (v ∷ vs) = valid t v ∧ validArguments ts vs
  validArguments _ _ = false

  validEntries : Type → Type → List Value → Bool
  validEntries k v [] = true
  validEntries k v (tuple (x ∷ y ∷ []) ∷ xs) = valid k x ∧ valid v y ∧ validEntries k v xs
  validEntries k v _ = false

  validElements : Type → List Value → Bool
  validElements t [] = true
  validElements t (x ∷ xs) = valid t x ∧ validElements t xs

u8T u32T u64T u128T fieldT b32T b64T b192T : Type
u8T = natural (2 ^ 8)
u32T = natural (2 ^ 32)
u64T = natural (2 ^ 64)
u128T = natural (2 ^ 128)
fieldT = natural fieldOrder
b32T = byteString 32
b64T = byteString 64
b192T = byteString 192

pointT : Curve → Type
pointT jubjub = product (fieldT ∷ fieldT ∷ [])
pointT k256 = foreignPoint k256
pointT p256 = foreignPoint p256

signatureT : Curve → Type
signatureT jubjub = product (pointT jubjub ∷ fieldT ∷ [])
signatureT k256 = product (natural k256ScalarOrder ∷ natural k256ScalarOrder ∷ [])
signatureT p256 = product (natural p256ScalarOrder ∷ natural p256ScalarOrder ∷ [])

-- Compact product layouts (zero-based declaration order):
-- policy:       [rp_id_hash, origin]
-- p256Auth:     [pk, use_counter, policy, authenticator_data, signature]
-- p256GrantAuth:[pk, policy, authenticator_data, signature]
-- coin:         [nonce, color, value]; qualifiedCoin additionally has mt_index.
-- GrantScope and GrantRecord fields are named in FullAccountLayouts; scopeT
-- and grantT below validate exactly those projection layouts.
policyT p256AuthT p256GrantAuthT coinT qualifiedCoinT scopeT grantT : Type
policyT = product (b32T ∷ byteString 21 ∷ [])
p256AuthT = product (pointT p256 ∷ u64T ∷ policyT ∷ byteString 37 ∷ signatureT p256 ∷ [])
p256GrantAuthT = product (pointT p256 ∷ policyT ∷ byteString 37 ∷ signatureT p256 ∷ [])
coinT = product (b32T ∷ b32T ∷ u128T ∷ [])
qualifiedCoinT = product (b32T ∷ b32T ∷ u128T ∷ u64T ∷ [])
scopeT = product (boolean ∷ boolean ∷ boolean ∷ boolean ∷ b32T ∷ u128T ∷ u128T ∷ u64T ∷
  b32T ∷ b32T ∷ u64T ∷ u128T ∷ b32T ∷ [])
grantT = product (u32T ∷ u32T ∷ u64T ∷ u64T ∷ b32T ∷ u64T ∷ u128T ∷ boolean ∷ scopeT ∷ [])

-- Field names match Compact's ledger declarations. FullAccountTypes.initialState
-- gives constructor defaults under these same names; State is not positional.
stateSchema : List (String × Type)
stateSchema =
  ("round" , u64T) ∷ ("enc_key" , b32T) ∷ ("inbox" , mapping u64T b192T) ∷
  ("inbox_count" , u64T) ∷ ("unshielded_balances" , mapping b32T u128T) ∷
  ("spec_version" , u32T) ∷ ("devices" , finiteSet b32T) ∷
  ("device_epoch" , u32T) ∷ ("device_count" , u8T) ∷ ("auth_nonce" , u64T) ∷
  ("boot" , b32T) ∷ ("booted" , boolean) ∷ ("grants" , mapping b32T grantT) ∷
  ("grant_generation" , u32T) ∷ ("recovery_pk" , pointT jubjub) ∷
  ("recovery_phi" , mapping u8T fieldT) ∷ ("recovery_phi_len" , u8T) ∷
  ("recovery_session" , b32T) ∷ ("recovery_wrap" , b64T) ∷ ("recovery_version" , u32T) ∷
  ("pending_recovery" , boolean) ∷ ("pending_entry" , b32T) ∷
  ("pending_recovery_pk" , pointT jubjub) ∷ ("pending_not_before" , u64T) ∷ ("veto_window" , u64T) ∷ []

validState : State → Bool
validState s = (length (ledger s) ≡ᵇ length stateSchema) ∧ check stateSchema
  ∧ unique (map (λ { (k , _) → bytes (ascii k) }) (ledger s))
  where
  check : List (String × Type) → Bool
  check [] = true
  check ((k , t) ∷ xs) = valid t (cell k s) ∧ check xs

validContext : Context → Bool
validContext ctx = valid b32T (self ctx) ∧ (blockTime ctx <ᵇ (2 ^ 64)) ∧ callerValid (caller ctx)
  where
  callerValid : Value → Bool
  callerValid none = true
  callerValid (some (tuple (bool _ ∷ address ∷ []))) = valid b32T address
  callerValid _ = false

module AccountSemantics (P : Primitives) where
  open import Conformance.FullAccountBody P
  open import Conformance.FullAccountCrypto P
  open import Conformance.FullAccountGrant P

  data Entrypoint : Set where
    construct : Entrypoint
    activation : Curve → Entrypoint
    device : Curve → Operation → Entrypoint
    grant : Curve → Operation → Entrypoint
    depositPublic depositPrivate submitRecovery finaliseRecovery : Entrypoint

  operations : List Operation
  operations = withdrawUnshielded ∷ withdrawShielded ∷ withdrawToContract ∷ appendInbox ∷
    rotateEncKey ∷ addDevice ∷ removeDevice ∷ issueGrant ∷ revokeGrant ∷ revokeAllGrants ∷
    publishRecovery ∷ cancelRecovery ∷ []

  spendOperations : List Operation
  spendOperations = withdrawUnshielded ∷ withdrawShielded ∷ withdrawToContract ∷ []

  runtimeForArm : Curve → List (String × Entrypoint)
  runtimeForArm c =
    (("activate_initial_device_with_" ++ˢ curveName c , activation c) ∷ []) ++
    map (λ op → operationName op ++ˢ "_with_" ++ˢ curveName c , device c op) operations ++
    map (λ op → operationName op ++ˢ "_with_grant_" ++ˢ curveName c , grant c op) spendOperations

  runtimeEntrypoints : List (String × Entrypoint)
  runtimeEntrypoints = runtimeForArm jubjub ++ runtimeForArm k256 ++ runtimeForArm p256 ++
    (("deposit_unshielded" , depositPublic) ∷ ("deposit_shielded" , depositPrivate) ∷
     ("recover_submit" , submitRecovery) ∷ ("recover_finalise" , finaliseRecovery) ∷ [])

  entrypoints : List (String × Entrypoint)
  entrypoints = ("constructor" , construct) ∷ runtimeEntrypoints

  lookupEntrypoint : String → List (String × Entrypoint) → Maybe Entrypoint
  lookupEntrypoint n [] = nothing
  lookupEntrypoint n ((k , e) ∷ es) = if stringEqual n k then just e else lookupEntrypoint n es

  -- Prefix layouts are documented beside FullAccountBody.operationAtoms;
  -- authSchema/grantSchema append the authentication suffixes defined below.
  operationSchema : Operation → List Type
  operationSchema withdrawUnshielded = b32T ∷ u128T ∷ b32T ∷ []
  operationSchema withdrawShielded = b32T ∷ b32T ∷ u128T ∷ []
  operationSchema withdrawToContract = b32T ∷ b32T ∷ u128T ∷ []
  operationSchema appendInbox = b192T ∷ []
  operationSchema rotateEncKey = b32T ∷ []
  operationSchema addDevice = b32T ∷ []
  operationSchema removeDevice = b32T ∷ []
  operationSchema issueGrant = b32T ∷ boolean ∷ boolean ∷ boolean ∷ boolean ∷ b32T ∷ u8T ∷
    b32T ∷ u128T ∷ u128T ∷ u128T ∷ u64T ∷ b32T ∷ b32T ∷ u64T ∷ u128T ∷ optional b32T ∷ b32T ∷ []
  operationSchema revokeGrant = b32T ∷ []
  operationSchema revokeAllGrants = []
  operationSchema publishRecovery = pointT jubjub ∷ b32T ∷ fieldT ∷ fieldT ∷ fieldT ∷ fieldT ∷ u8T ∷ b64T ∷ []
  operationSchema cancelRecovery = []

  -- Device authentication suffixes:
  -- jubjub: [pk, use_counter, sig_r, sig_s, grind_nonce]
  -- k256:   [pk, use_counter, signature, envelope]
  -- p256:   [p256Auth] using the product layout above.
  authSchema : Curve → List Type
  authSchema jubjub = pointT jubjub ∷ u64T ∷ pointT jubjub ∷ fieldT ∷ u64T ∷ []
  authSchema k256 = pointT k256 ∷ u64T ∷ signatureT k256 ∷ u8T ∷ []
  authSchema p256 = p256AuthT ∷ []

  -- Grant authentication suffixes (shielded change_entry/enc_key precede these):
  -- jubjub: [pk, origin, slot, salt, recipient_kind, recipient, max_coin_value,
  --          spent_prev, sig_r, sig_s, grind_nonce]
  -- k256:   [pk, envelope, origin, slot, salt, recipient_kind, recipient,
  --          max_coin_value, spent_prev, signature]
  -- p256:   [origin, slot, salt, recipient_kind, recipient, max_coin_value,
  --          spent_prev, p256GrantAuth].
  grantSchema : Curve → List Type
  grantSchema jubjub = pointT jubjub ∷ b32T ∷ u8T ∷ b32T ∷ u8T ∷ b32T ∷ u128T ∷ u128T ∷ pointT jubjub ∷ fieldT ∷ u64T ∷ []
  grantSchema k256 = pointT k256 ∷ u8T ∷ b32T ∷ u8T ∷ b32T ∷ u8T ∷ b32T ∷ u128T ∷ u128T ∷ signatureT k256 ∷ []
  grantSchema p256 = b32T ∷ u8T ∷ b32T ∷ u8T ∷ b32T ∷ u128T ∷ u128T ∷ p256GrantAuthT ∷ []

  -- Constructor: [boot, enc_key, recovery_pk, recovery_wrap, veto_window].
  -- Activation: [pk, boot_salt], plus envelope (k256) or policy (p256).
  -- Deposits: [color, amount] or [coin, inbox_entry].
  -- Recovery submission: SubmitArguments in FullAccountLayouts (10 fields).
  schema : Entrypoint → List Type
  schema construct = b32T ∷ b32T ∷ pointT jubjub ∷ b64T ∷ u64T ∷ []
  schema (activation jubjub) = pointT jubjub ∷ b32T ∷ []
  schema (activation k256) = pointT k256 ∷ b32T ∷ u8T ∷ []
  schema (activation p256) = pointT p256 ∷ b32T ∷ policyT ∷ []
  schema (device c op) = operationSchema op ++ authSchema c
  schema (grant c withdrawUnshielded) = operationSchema withdrawUnshielded ++ grantSchema c
  schema (grant c op) = operationSchema op ++ (b192T ∷ b32T ∷ grantSchema c)
  schema depositPublic = b32T ∷ u128T ∷ []
  schema depositPrivate = coinT ∷ b192T ∷ []
  schema submitRecovery = pointT jubjub ∷ pointT jubjub ∷ u32T ∷ u64T ∷ u64T ∷ pointT jubjub ∷ fieldT ∷ pointT jubjub ∷ fieldT ∷ u64T ∷ []
  schema finaliseRecovery = []

  parseAuth : Curve → List Value → Auth
  parseAuth jubjub xs = auth (get 0 xs) (number (get 1 xs)) (get 2 xs) (get 3 xs) (number (get 4 xs)) 0 none none none
  parseAuth k256 xs = auth (get 0 xs) (number (get 1 xs)) none none 0 (number (get 3 xs)) none none (get 2 xs)
  parseAuth p256 xs =
    let a = get 0 xs in auth (at 0 a) (number (at 1 a)) none none 0 0 (at 2 a) (at 3 a) (at 4 a)

  parseActivation : Curve → List Value → Auth
  parseActivation jubjub xs = auth (get 0 xs) 0 none none 0 0 none none none
  parseActivation k256 xs = auth (get 0 xs) 0 none none 0 (number (get 2 xs)) none none none
  parseActivation p256 xs = auth (get 0 xs) 0 none none 0 0 (get 2 xs) none none

  parseGrant : Curve → List Value → Value → Value → GrantAuth
  parseGrant jubjub xs change encryption = grantAuth
    (auth (get 0 xs) 0 (get 8 xs) (get 9 xs) (number (get 10 xs)) 0 none none none)
    (get 1 xs) (number (get 2 xs)) (get 3 xs) (get 4 xs) (get 5 xs)
    (number (get 6 xs)) (number (get 7 xs)) change encryption
  parseGrant k256 xs change encryption = grantAuth
    (auth (get 0 xs) 0 none none 0 (number (get 1 xs)) none none (get 9 xs))
    (get 2 xs) (number (get 3 xs)) (get 4 xs) (get 5 xs) (get 6 xs)
    (number (get 7 xs)) (number (get 8 xs)) change encryption
  parseGrant p256 xs change encryption =
    let a = get 7 xs in grantAuth
      (auth (at 0 a) 0 none none 0 0 (at 1 a) (at 2 a) (at 3 a))
      (get 0 xs) (number (get 1 xs)) (get 2 xs) (get 3 xs) (get 4 xs)
      (number (get 5 xs)) (number (get 6 xs)) change encryption

  needsCoin : Entrypoint → Bool
  needsCoin (device _ op) = shielded op
  needsCoin (grant _ op) = shielded op
  needsCoin _ = false

  callerEntryAfter : Curve → Operation → Context → Auth → Value → M Value
  callerEntryAfter c removeDevice ctx a cached = do
    addr ← readSelf ctx
    epoch ← readCount "device_epoch"
    count ← cast "use_counter" 64 (suc (counter a))
    entryAt c addr a epoch count
  callerEntryAfter c op ctx a cached = return cached

  deviceCall : Curve → Operation → Context → List Value → M Value
  deviceCall c op ctx xs = do
    let n = length (operationSchema op)
    let args = take n xs
    let a = parseAuth c (drop n xs)
    coin ← (if shielded op then held ctx (get 1 args) else return none)
    atoms ← operationAtoms op args coin
    addr ← readSelf ctx
    nonce ← readCount "auth_nonce"
    h ← challengeAt c false (operationName op) addr a atoms nonce
    postEntry ← authorise c ctx a h
    callerEntry ← callerEntryAfter c op ctx a postEntry
    body op ctx args coin callerEntry

  constructorAssignments : List String
  constructorAssignments = "round" ∷ "enc_key" ∷ "inbox_count" ∷ "spec_version" ∷
    "boot" ∷ "booted" ∷ "device_epoch" ∷ "device_count" ∷ "auth_nonce" ∷
    "grant_generation" ∷ "recovery_pk" ∷ "recovery_phi_len" ∷ "recovery_session" ∷
    "recovery_wrap" ∷ "recovery_version" ∷ "pending_recovery" ∷ "pending_entry" ∷
    "pending_recovery_pk" ∷ "pending_not_before" ∷ "veto_window" ∷ []

  execute : Entrypoint → Context → List Value → M Value
  execute construct ctx xs s =
    let initial = initialState (get 0 xs) (get 1 xs) (get 2 xs) (get 3 xs) (number (get 4 xs))
    in accepted unit initial (map (λ k → writeCell k (cell k initial)) constructorAssignments)
  execute (activation c) ctx xs = activate c ctx (parseActivation c xs) (get 1 xs)
  execute (device c op) ctx xs = deviceCall c op ctx xs
  execute (grant c withdrawUnshielded) ctx xs =
    grantCall c withdrawUnshielded ctx (parseGrant c (drop 3 xs) none none) (take 3 xs)
  execute (grant c op) ctx xs =
    grantCall c op ctx (parseGrant c (drop 5 xs) (get 3 xs) (get 4 xs)) (take 3 xs)
  execute depositPublic ctx xs = do
    emit (receiveUnshielded (get 0 xs) (number (get 1 xs)))
    credit (get 0 xs) (number (get 1 xs))
    bump "round" 64
    return unit
  execute depositPrivate ctx xs = do
    receiveCoin ctx (get 0 xs)
    inboxAppend (get 1 xs)
    bump "round" 64
    return unit
  execute submitRecovery ctx xs = submit ctx xs
  execute finaliseRecovery ctx xs = finalise ctx

  checked : Entrypoint → Context → List Value → State → Execution Value
  checked e ctx xs s =
    if validArguments (schema e) xs then
      if validContext ctx then
        if needsCoin e ∧ not (valid qualifiedCoinT (heldCoin ctx)) then rejected (decoding "held_coin return") else
          stateChecked e
      else rejected (decoding "runtime context")
    else rejected (decoding "circuit arguments")
    where
    stateChecked : Entrypoint → Execution Value
    stateChecked construct = execute construct ctx xs s
    stateChecked e = if validState s then execute e ctx xs s else rejected (decoding "ledger state")

  dispatch : Context → RawCall → State → Execution Value
  dispatch ctx call s with lookupEntrypoint (name call) entrypoints
  ... | nothing = rejected (decoding "unknown runtime circuit")
  ... | just e = checked e ctx (arguments call) s

-- This is the executable adapter entry point, including the constructor.
dispatch : Primitives → Context → RawCall → State → Execution Value
dispatch P = AccountSemantics.dispatch P

runtimeNames : Primitives → List String
runtimeNames P = map proj₁ (AccountSemantics.runtimeEntrypoints P)
