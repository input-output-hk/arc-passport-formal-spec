{-# OPTIONS --safe --without-K --guardedness #-}

module Midnight.ContractDSL.PrivacyReplacement where

open import Data.Nat.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Level

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol; _∘ᵖ_)
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Compose
import CategoricalCrypto.UC.Model.Setup as Exact
import CategoricalCrypto.UC.Model.Family as Family
open import CategoricalCrypto.UC.Model.Seal
import CategoricalCrypto.UC.Robust as Robust
open import CategoricalCrypto.UCSetup
open import Midnight.ContractDSL.Ledger
import Midnight.ContractDSL.Program as Programs
import Midnight.ContractDSL.Protocol as DSL

-- Simulator closure is essential: UC does not preserve arbitrary predicates
-- of hidden state or properties restricted to an honest adversary.
module Transfer
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
  (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where

  open Robust setup

  module Replacement {A B : 𝒞.Obj} {X Y : ℐ.Obj}
    (real : A 𝒞.⇒ T₀ X B) (ideal : A 𝒞.⇒ T₀ Y B)
    (emulates : real ≤UC ideal) where

    -- Extract at the resource boundary, before choosing either challenge context.
    simulator : Y ℐ.⇒ X
    simulator = proj₁ (≤UC⇒dummy emulates)

    resource-simulation : real ≈ᵁ sub simulator 𝒞.∘ ideal
    resource-simulation = proj₂ (≤UC⇒dummy emulates)

    context-simulation : {C : 𝒞.Obj} {Z : ℐ.Obj}
      (context : B 𝒞.⇒ T₀ Z C) →
      context ∙ real ≈ᵁ sub (simulator ⊗₁ ℐ.id) 𝒞.∘ (context ∙ ideal)
    context-simulation context = ≈ᵁ-trans (ext-cong context resource-simulation)
      (≈C⇒≈ᵁ (let open 𝒞 in
        sym-assoc ○ (sub-commute₁ ⟩∘⟨refl) ○ assoc))

    simulated-observation : {C : 𝒞.Obj} {Z : ℐ.Obj}
      (context : B 𝒞.⇒ T₀ Z C) (W : ℐ.Obj)
      (e : Env (T₀ (W ⊗₀ (X ⊗₀ Z)) C)) →
      run W (context ∙ real) e Env.≈
        run W (context ∙ ideal) (regradeEnv W (simulator ⊗₁ ℐ.id) e)
    simulated-observation context W e =
      Env.trans (KE.run∼ (context-simulation context W))
        (run-sub W (simulator ⊗₁ ℐ.id) (context ∙ ideal) e)

    module TwoWorld {C : 𝒞.Obj} {Z : ℐ.Obj}
      (left right : B 𝒞.⇒ T₀ Z C) where

      transfer-observation : (W : ℐ.Obj)
        (e : Env (T₀ (W ⊗₀ (X ⊗₀ Z)) C)) →
        run W (left ∙ ideal) (regradeEnv W (simulator ⊗₁ ℐ.id) e) Env.≈
          run W (right ∙ ideal) (regradeEnv W (simulator ⊗₁ ℐ.id) e) →
        run W (left ∙ real) e Env.≈ run W (right ∙ real) e
      transfer-observation W e privacy =
        Env.trans (simulated-observation left W e)
          (Env.trans privacy (Env.sym (simulated-observation right W e)))

      transfer-private : {d : Level} (Adm : Admissible C d) →
        ((s : Y ℐ.⇒ X) → ∀ W e → Adm W (X ⊗₀ Z) e →
          run W (left ∙ ideal) (regradeEnv W (s ⊗₁ ℐ.id) e) Env.≈
            run W (right ∙ ideal) (regradeEnv W (s ⊗₁ ℐ.id) e)) →
        ∀ W e → Adm W (X ⊗₀ Z) e →
          run W (left ∙ real) e Env.≈ run W (right ∙ real) e
      transfer-private Adm privacy W e admissible =
        transfer-observation W e (privacy simulator W e admissible)

      transfer-closed : {d : Level} (Adm : Admissible C d) →
        ((s : Y ℐ.⇒ X) → ClosedUnder Adm (s ⊗₁ ℐ.id)) →
        (∀ W e → Adm W (Y ⊗₀ Z) e →
          run W (left ∙ ideal) e Env.≈ run W (right ∙ ideal) e) →
        ∀ W e → Adm W (X ⊗₀ Z) e →
          run W (left ∙ real) e Env.≈ run W (right ∙ real) e
      transfer-closed Adm closed privacy =
        transfer-private Adm (λ s W e admissible →
          privacy W (regradeEnv W (s ⊗₁ ℐ.id) e) (closed s W e admissible))

    module InContext {C : 𝒞.Obj} {Z : ℐ.Obj}
      (context : B 𝒞.⇒ T₀ Z C) where

      realSystem : A 𝒞.⇒ T₀ (X ⊗₀ Z) C
      realSystem = context ∙ real

      idealSystem : A 𝒞.⇒ T₀ (Y ⊗₀ Z) C
      idealSystem = context ∙ ideal

      system-emulates : realSystem ≤UC idealSystem
      system-emulates = UC-compose emulates (≤UC-refl context)

      transfer : {p d : Level} (P : Predℰ A p) (Adm : Admissible C d) →
        ((s : (Y ⊗₀ Z) ℐ.⇒ (X ⊗₀ Z)) → ClosedUnder Adm s) →
        Robust P Adm idealSystem → Robust P Adm realSystem
      transfer P Adm closed = uc-preserves P Adm closed system-emulates

      transfer-unrestricted : {p : Level} (P : Predℰ A p) →
        Robust P ⊤ᴬ idealSystem → Robust P ⊤ᴬ realSystem
      transfer-unrestricted P = transfer P ⊤ᴬ (λ _ _ _ _ → tt)

module ExactTransfer = Transfer Exact.StdSetup
module ComputationalTransfer = Transfer Family.Canonicalᴺ.StdSetup

-- Compiling the honest context adds only a unit adversary interface.
module ForProtocol {S B : Iface} (context : Protocol S B) where
  open Exact hiding (S)

  client : ifaceᵒ S ⇒ T₀ ℐ.unit (ifaceᵒ B)
  client = return ∘ procᵒ (morphism context)

  module WithResources {A X Y : Channel}
    (real : A ⇒ T₀ X (ifaceᵒ S))
    (ideal : A ⇒ T₀ Y (ifaceᵒ S))
    (emulates : real ≤UC ideal) where
    module R = ExactTransfer.Replacement real ideal emulates
    open R.InContext client public

  module WithProtocols {A X Y : Iface}
    (real : Protocol A (X ⊗ᴵ S))
    (ideal : Protocol A (Y ⊗ᴵ S))
    (emulates : gradedᵒ (morphism real) ≤UC gradedᵒ (morphism ideal)) where
    open WithResources (gradedᵒ (morphism real)) (gradedᵒ (morphism ideal)) emulates public

  -- The categorical assembly is the compiled native composition, up to the
  -- unit-grade coherence map; no second operational semantics is introduced.
  compiled-assembly : {A : Iface} (backend : Protocol A S) →
    sub λ⇒ ∘ (client ∙ (return ∘ procᵒ (morphism backend)))
      ≈ return ∘ procᵒ (morphism (context ∘ᵖ backend))
  compiled-assembly backend = 𝒞.Equiv.trans (∙-return client (procᵒ (morphism backend)))
    (𝒞.Equiv.trans 𝒞.assoc
      (𝒞.∘-resp-≈ʳ (𝒞.Equiv.sym
        (𝒞.Equiv.trans (≈ᴹ⇒≈ᵒ (morphismCompose context backend))
          (procᵒ-∘ (morphism context) (morphism backend))))))

module ForContract (L : Semantics) (Assertion : Set)
  (contract : DSL.Contract L Assertion)
  (communication : DSL.CommunicationScheme L Assertion contract) (self : ℕ) =
  ForProtocol (DSL.Interpreter.toProtocol L Assertion contract communication self)

module ForProgram (L : Semantics) (Assertion : Set) {A : Set}
  (program : Programs.Program L Assertion A) (self : ℕ) =
  ForProtocol (DSL.programToProtocol L Assertion program self)
