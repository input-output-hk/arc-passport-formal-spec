-- Midnight.Passport.Channels
--
-- Legacy message vocabulary for selected Passport interfaces. ChannelSpec
-- names the two directions of a message pair; it is not a categorical-crypto
-- Channel and does not define the wiring in Midnight.Passport.Semantics.

module Midnight.Passport.Channels where

open import Data.String using (String)

open import Midnight.Passport.Core

------------------------------------------------------------------------
-- Channel specification record

record ChannelSpec : Set₁ where
  field
    name    : String   -- human-readable interface identifier
    inType  : Set      -- type of messages flowing INTO the component
    outType : Set      -- type of messages flowing OUT OF the component

------------------------------------------------------------------------
-- Message types
--
-- Each message type is postulated here.  Concrete record definitions
-- will replace these postulates as each component is specified in its
-- own module.

-- ── Authentication path (C9 → C5 → C6 → C1) ────────────────────────

-- User-facing authentication request (top of the auth path).
postulate
  UserAuthRequest  : Set   -- { rpId, challenge, origin }
  UserAuthResponse : Set   -- { assertion, clientDataJSON }

-- WebAuthn passkey challenge sent to the authenticator (C9 DeviceAuth).
postulate
  DeviceChallenge : Set   -- { rpId, challenge : Bytes 32 }

-- PRF output from the WebAuthn PRF extension; becomes the device key
-- material fed into C5 Signing.
postulate
  PRFOutput : Set   -- { prf : Bytes 32 }

-- A request to produce a Schnorr signature (C5 → C6 interface).
postulate
  SignRequest : Set   -- { payload : Bytes 32, pubKey : PubKey }

-- Schnorr signature response.
Signature : Set
Signature = SchnorrSig

-- A request to build a circuit witness for the ZK prover (C7 → C6).
postulate
  WitnessRequest  : Set   -- { sigRequest, zkStatement }
  WitnessResponse : Set   -- { witness : private inputs }

-- Proof submission to the on-chain account contract (C6 → C1).
postulate
  ProofSubmission : Set   -- { proof : ZKProof, statement : Statement }

-- On-chain transaction result (C1 → chain boundary).
postulate
  TxResult : Set   -- { txId : Bytes 32, status : Bool }

-- Chain-level write / event pair (C1 → ledger).
postulate
  LedgerWrite  : Set   -- { txBody : Bytes n }
  ChainEvent   : Set   -- { blockHeight : ℕ, txId : Bytes 32 }

-- Outer chain boundary (User ⟷ chain, end-to-end).
postulate
  UserRequest  : Set   -- top-level user intent
  ChainResult  : Set   -- on-chain outcome visible to the user

-- ── Grant path (dApp → C10 → C12 → C1) ─────────────────────────────

-- Grant request from a dApp (dApp → C10).
postulate
  GrantRequest  : Set   -- { scope : List String, grantSecret : GrantSecret }
  GrantResponse : Set   -- { commitment : Commitment }

-- ── Credential path (C18 → C20 / C21) ───────────────────────────────

-- Merkle path from C18 AttestationTree to C20 SelectiveDisclosure.
postulate
  MerklePath : Set   -- { leaf : 𝔽, siblings : List 𝔽, root : 𝔽 }

-- Merkle root returned after path verification.
postulate
  RootHash : Set   -- { root : 𝔽 }

-- Nullifier check request/response (C21 ↔ execution environment).
postulate
  NullifierMsg      : Set   -- { context : Bytes 32, credential : 𝔽 }
  NullifierResponse : Set   -- { fresh : Bool }

------------------------------------------------------------------------
-- Channel specification values

-- ── Authentication path ─────────────────────────────────────────────

-- Top-of-stack: user initiates authentication.
User-C9 : ChannelSpec
User-C9 = record
  { name    = "User-C9"
  ; inType  = UserAuthRequest
  ; outType = UserAuthResponse
  }

-- C9 DeviceAuth hands a WebAuthn challenge down to the passkey
-- authenticator and receives the PRF-derived device key.
C9-C5 : ChannelSpec
C9-C5 = record
  { name    = "C9-C5"
  ; inType  = DeviceChallenge
  ; outType = PRFOutput
  }

-- C5 Signing requests a Schnorr signature from the device key material
-- and returns it to C6 ProofGeneration.
C5-C6 : ChannelSpec
C5-C6 = record
  { name    = "C5-C6"
  ; inType  = SignRequest
  ; outType = Signature
  }

-- C7 WitnessHandling prepares the private witness for the ZK circuit.
C7-C6 : ChannelSpec
C7-C6 = record
  { name    = "C7-C6"
  ; inType  = WitnessRequest
  ; outType = WitnessResponse
  }

-- C6 ProofGeneration submits the finished ZK proof to C1
-- AccountCustody.
C6-C1 : ChannelSpec
C6-C1 = record
  { name    = "C6-C1"
  ; inType  = ProofSubmission
  ; outType = TxResult
  }

-- C1 AccountCustody writes the transaction to the ledger and listens
-- for chain events.
C1-Chain : ChannelSpec
C1-Chain = record
  { name    = "C1-Chain"
  ; inType  = LedgerWrite
  ; outType = ChainEvent
  }

-- Outer boundary of the full authentication path.
User-Chain : ChannelSpec
User-Chain = record
  { name    = "User-Chain"
  ; inType  = UserRequest
  ; outType = ChainResult
  }

-- ── Grant path ───────────────────────────────────────────────────────

-- dApp initiates a scoped grant request.
dApp-C10 : ChannelSpec
dApp-C10 = record
  { name    = "dApp-C10"
  ; inType  = GrantRequest
  ; outType = GrantResponse
  }

-- ── Credential path ──────────────────────────────────────────────────

-- C18 AttestationTree delivers a Merkle inclusion path to C20
-- SelectiveDisclosure.
C18-C20 : ChannelSpec
C18-C20 = record
  { name    = "C18-C20"
  ; inType  = MerklePath
  ; outType = RootHash
  }

-- C21 Nullifier checks replay-prevention against the execution
-- environment.
C21-env : ChannelSpec
C21-env = record
  { name    = "C21-env"
  ; inType  = NullifierMsg
  ; outType = NullifierResponse
  }
