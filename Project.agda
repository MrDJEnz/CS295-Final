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

-- Define XNOR
_XNOR_ : 𝔹 → 𝔹 → 𝔹
O XNOR O = I
O XNOR I = O
I XNOR O = O
I XNOR I = I

    
-- Define the Sequence either 0 or 1 to make sure the pkt received is correct
record Seq (SnumOne SnumTwo : Set) : Set where {- A Sequence -}
  constructor _,_
  field
    SeqZer : 𝔹  -- Sequence number is either 0 ... false
    SeqOne : 𝔹  -- 1 ... true


-- the message that will be sent from src → dest with info
record msg : Set where
  field
    source : principal
    destination : principal
    information : ℕ
    sequence : Seq 𝔹 𝔹

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


sequence00 : Seq 𝔹 𝔹
sequence00 = O , O

sequence01 : Seq 𝔹 𝔹
sequence01 = O , I

sequence10 : Seq 𝔹 𝔹
sequence10 = I , O

sequence11 : Seq 𝔹 𝔹
sequence11 = I , I
-------------------------------------------------------------------------------------
-- If the sender sent packet 0 we check status by seeing if we have packet 0 returned
-- If the packet 0 is returned we move to SeqOne

-- If sender sent pkt 1 check status if pkt 1 returned
-- If pkt 1 is returned move to SeqZero

-- check sender sequence state
infix 99 _sender-seq-status_
data _sender-seq-status_ : 𝔹 →  𝔹  → Set where
  SeqZeroZero : ∀{SeqZero} → SeqZero sender-seq-status SeqZero
  SeqZeroOne : ∀{SeqZero SeqOne} → SeqZero sender-seq-status SeqOne
  SeqOneZero : ∀{SeqZero SeqOne} → SeqOne sender-seq-status SeqZero
  SeqOneOne : ∀{SeqOne} → SeqOne sender-seq-status SeqOne

-- check receiver sequence state
infix 100 _recv-seq-status_
data _recv-seq-status_ : 𝔹 →  𝔹  → Set where
  SeqZeroZero : ∀{SeqZero} → SeqZero recv-seq-status SeqZero
  SeqZeroOne : ∀{SeqZero SeqOne} → SeqZero recv-seq-status SeqOne
  SeqOneZero : ∀{SeqZero SeqOne} → SeqOne recv-seq-status SeqZero
  SeqOneOne : ∀{SeqOne} → SeqOne recv-seq-status SeqOne
-------------------------------------------------------------------------------------

-- Define a sent packet and determine seq-state
seq-state-snd : (seq-stat-fst seq-stat-scnd : 𝔹) → (seq-stat-fst sender-seq-status seq-stat-scnd)
seq-state-snd I I = SeqOneOne
seq-state-snd I O = SeqOneZero
seq-state-snd O I = SeqZeroOne
seq-state-snd O O = SeqZeroZero

_ : seq-state-snd O O ≡ SeqZeroZero
_ = ↯

_ : seq-state-snd O I ≡ SeqZeroOne
_ = ↯

_ : seq-state-snd I O ≡ SeqOneZero
_ = ↯

_ : seq-state-snd I I ≡ SeqOneOne
_ = ↯

rec-state-snd : (seq-stat-fst seq-stat-scnd : 𝔹) → (seq-stat-fst sender-seq-status seq-stat-scnd)
rec-state-snd I I = SeqOneOne
rec-state-snd I O = SeqOneZero
rec-state-snd O I = SeqZeroOne
rec-state-snd O O = SeqZeroZero

_ : rec-state-snd O O ≡ SeqZeroZero
_ = ↯

_ : rec-state-snd O I ≡ SeqZeroOne
_ = ↯

_ : rec-state-snd I O ≡ SeqOneZero
_ = ↯

_ : rec-state-snd I I ≡ SeqOneOne
_ = ↯
------------------------------------------------------------------------------------------
-- Send a message
send-msg : (sender-node recv-node : principal) (msg-byte : ℕ) (window-seq : Seq 𝔹 𝔹) → 𝔹
send-msg sender-node recv-node Z (SeqZer , SeqOne) = {!!}
send-msg sender-node recv-node (S msg-byte) (SeqZer , SeqOne) = {!!}

_ : send-msg Sender Receiver 0 sequence00 ≡ I
_ = ↯

_ : send-msg Sender Receiver 0 sequence10 ≡ O
_ = ↯

_ : send-msg Sender Receiver 0 sequence01 ≡ O
_ = ↯

_ : send-msg Sender Receiver 0 sequence11 ≡ I
_ = ↯

  
 

