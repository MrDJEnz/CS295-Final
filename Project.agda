module Project where
open import Basics001

{-  
-- relational semantics
data transition : system-state → system-state → Set
  receive-msg :
    → m ∈ nt
    → source m ≡ Sender
    → destination m ≡ Receiver
    → transition ⟨ t , sb , rb , nt ⟩ → ⟨ t + 1 , sb , (⟨ t , information m ⟩ ∷ rb) , nt - m ⟩

-- interpreter that you could run (might be nicer to define)
transition : system-state → ℘ system-state
transition ⟨ t , sb , rb , nt ⟩ = …
-}
-- Define the Sender and receiver Networks
data principal : Set where
  Sender : principal
  Receiver : principal

    
-- Define the Sequence either 0 or 1 to make sure the pkt received is correct
record Seq (SnumOne SnumTwo : Set) : Set where {- A Sequence -}
  constructor _,_
  field
    SeqZer : ℕ  -- Sequence number is either 0 
    SeqOne : ℕ  -- 1


-- the message that will be sent from src → dest with info
record msg : Set where
  field
    source : principal
    destination : principal
    information : ℕ
    sequence : Seq ℕ ℕ

-- Define the state of our system
record system-state : Set where
  constructor ⟨_,_,_,_⟩
  field
    time : ℕ
    sender-buffer : list (ℕ ∧ ℕ)
    receiver-buffer : list (ℕ ∧ ℕ)
    network-traffic : list msg

-- Define the state of transmission
data trans-state : Set where
  waiting : trans-state
  ready : trans-state

-- Define the send state
data send-state : Set where
   ready : send-state 
   wait  : send-state 
   timeout : send-state
   sent  : send-state


sequence00 : Seq ℕ ℕ
sequence00 = 0 , 0

sequence01 : Seq ℕ ℕ
sequence01 = 0 , 1

sequence10 : Seq ℕ ℕ
sequence10 = 1 , 0

sequence11 : Seq ℕ ℕ
sequence11 = 1 , 1
-------------------------------------------------------------------------------------
-- If the sender sent packet 0 we check status by seeing if we have packet 0 returned
-- If the packet 0 is returned we move to SeqOne

-- If sender sent pkt 1 check status if pkt 1 returned
-- If pkt 1 is returned move to SeqZero

-- check sender sequence state
infix 99 _sender-seq-status_
data _sender-seq-status_ : ℕ →  ℕ  → Set where
  SeqZeroZero : ∀{SeqZero} → SeqZero sender-seq-status SeqZero
  SeqZeroOne : ∀{SeqZero SeqOne} → SeqZero sender-seq-status SeqOne
  SeqOneZero : ∀{SeqZero SeqOne} → SeqOne sender-seq-status SeqZero
  SeqOneOne : ∀{SeqOne} → SeqOne sender-seq-status SeqOne

-- check receiver sequence state
infix 100 _recv-seq-status_
data _recv-seq-status_ : ℕ →  ℕ  → Set where
  SeqZeroZero : ∀{SeqZero} → SeqZero recv-seq-status SeqZero
  SeqZeroOne : ∀{SeqZero SeqOne} → SeqZero recv-seq-status SeqOne
  SeqOneZero : ∀{SeqZero SeqOne} → SeqOne recv-seq-status SeqZero
  SeqOneOne : ∀{SeqOne} → SeqOne recv-seq-status SeqOne
-------------------------------------------------------------------------------------

-- Define a sent packet and determine seq-state
seq-state-snd : (seq-stat-fst seq-stat-scnd : ℕ) → (seq-stat-fst sender-seq-status seq-stat-scnd)
seq-state-snd Z Z = SeqZeroZero
seq-state-snd Z (S seq-stat-scnd) = SeqZeroOne
seq-state-snd (S seq-stat-fst) Z = SeqOneZero
seq-state-snd (S seq-stat-fst) (S seq-stat-scnd) = {!SeqOneOne!}

_ : seq-state-snd 0 0 ≡ SeqZeroZero
_ = ↯

_ : seq-state-snd 0 1 ≡ SeqZeroOne
_ = ↯

_ : seq-state-snd 1 0 ≡ SeqOneZero
_ = ↯

_ : seq-state-snd 1 1 ≡ SeqOneOne
_ = ↯
  
 

