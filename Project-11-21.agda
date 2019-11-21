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
data pk# : Set where
  pk0 : pk#
  pk1 : pk#
  

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
    SeqZer : SnumOne  -- Sequence number is either 0 
    SeqOne : SnumTwo  -- 1


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

-------------------------------------------------------------------------------------
-- If the sender sent packet 0 we check status by seeing if we have packet 0 returned
-- If the packet 0 is returned we move to SeqOne

-- If sender sent pkt 1 check status if pkt 1 returned
-- If pkt 1 is returned move to SeqZero

-- check sender sequence state
infix 99 _sender-seq-status_
data _sender-seq-status_ : 𝔹 →  𝔹  → Set where
  SeqZeroZero : ∀{blah} → blah sender-seq-status blah
  SeqZeroOne : ∀{bloo walter} → bloo sender-seq-status walter
  SeqOneZero : ∀{bloo walter} → walter sender-seq-status bloo
  SeqOneOne : ∀{walter} → walter sender-seq-status walter

-- check receiver sequence state
infix 100 _recv-seq-status_
data _recv-seq-status_ : 𝔹 →  𝔹  → Set where
  -- DCD: same possible issue as above
  SeqZeroZero : ∀{SeqZero} → SeqZero recv-seq-status SeqZero
  SeqZeroOne : ∀{SeqZero SeqOne} → SeqZero recv-seq-status SeqOne
  SeqOneZero : ∀{SeqZero SeqOne} → SeqOne recv-seq-status SeqZero
  SeqOneOne : ∀{SeqOne} → SeqOne recv-seq-status SeqOne


sequence00 : Seq pk# pk#
sequence00 = pk0 , pk0

sequence01 : Seq pk# pk#
sequence01 = pk0 , pk1

sequence10 : Seq pk# pk#
sequence10 = pk1 , pk0

sequence11 : Seq pk# pk#
sequence11 = pk1 , pk1
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

seq-state-recv : (seq-stat-fst seq-stat-scnd : 𝔹) → (seq-stat-fst recv-seq-status seq-stat-scnd)
seq-state-recv I I = SeqOneOne
seq-state-recv I O = SeqOneZero
seq-state-recv O I = SeqZeroOne
seq-state-recv O O = SeqZeroZero

_ : seq-state-recv O O ≡ SeqZeroZero
_ = ↯

_ : seq-state-recv O I ≡ SeqZeroOne
_ = ↯

_ : seq-state-recv I O ≡ SeqOneZero
_ = ↯

_ : seq-state-recv I I ≡ SeqOneOne
_ = ↯

get-seq : (window-send window-recv : pk#) → (Seq pk# pk#)
get-seq a b = a , b

_ : get-seq pk0 pk0 ≡ sequence00
_ = ↯

_ : get-seq pk1 pk0 ≡ sequence10
_ = ↯

_ : get-seq pk0 pk1 ≡ sequence01
_ = ↯

_ : get-seq pk1 pk1 ≡ sequence11
_ = ↯

------------------------------------------------------------------------------------------
-- Send a message
-- val1 val2 are used to get sequence 
send-msg : (sender-node recv-node : principal) (msg-byte : ℕ) (val1 val2 :  𝔹) → 𝔹
-- sender-node is not used
-- recv-node is not used
-- will they be in the future? if not remove them, or figure out how
-- they need to be used
send-msg sender-node recv-node msg-byte val1 val2 = val1 XNOR val2 

_ : send-msg Sender Receiver 0 O O  ≡ I
_ = ↯

_ : send-msg Sender Receiver 0 I O ≡ O
_ = ↯

_ : send-msg Sender Receiver 0 O I ≡ O
_ = ↯

_ : send-msg Sender Receiver 0 I I ≡ I
_ = ↯


-- this is just xnor on packets?
send-sp-pkt : (expecting actual : pk#) → pk#
send-sp-pkt pk0 pk0 = pk1
send-sp-pkt pk0 pk1 = pk0
send-sp-pkt pk1 pk0 = pk1
send-sp-pkt pk1 pk1 = pk0

_ : send-sp-pkt pk0 pk0 ≡ pk1
_ = ↯

_ : send-sp-pkt pk1 pk0 ≡ pk1
_ = ↯

_ : send-sp-pkt pk1 pk1 ≡ pk0
_ = ↯

_ : send-sp-pkt pk0 pk1 ≡ pk0
_ = ↯

record send-sp-pkt-msg : Set where
  field
    pk : pk#
    msg-bit : ℕ
------------------------------------------------------------------------------------------
-- Send a message with data stream.
-- testing with window sequence
send-msg-beta : (sender-node recv-node : principal) (msg-byte : ℕ) (window-snd window-rcv : pk#) → send-sp-pkt-msg
send-msg-beta sender-node recv-node msg-byte pk0 pk0 = record { pk = pk1 ; msg-bit = S(msg-byte)}
-- if expected nak is 0 and received nak is 0: then SUCCESS
-- send next ack num and next msg-byte
-- DCD: sender-node not used, but will probably be used when you interpret this as a change to the system stat

send-msg-beta sender-node recv-node msg-byte pk0 pk1 = record { pk = pk0 ; msg-bit = msg-byte }
-- if expected nak is 0 and received nak is 1: then we dropped a packed or have a dupe
-- send current ack again and current  msg-byte again

send-msg-beta sender-node recv-node msg-byte pk1 pk0 = record { pk = pk1 ; msg-bit = msg-byte }
-- if expected nak is 1 and received nak  0: then we dropped a packet or have a dupe
-- send current ack num and current msg-byte

send-msg-beta sender-node recv-node msg-byte pk1 pk1 = record { pk = pk0 ; msg-bit = S(msg-byte) }
-- if expected nak is 1 and received nak is 1: then SUCCESS
-- send next ack num and next msg-byte

_ : send-msg-beta Sender Receiver 0 pk0 pk0 ≡ record { pk = pk1 ; msg-bit = 1} -- expecting0 receive0 send next byte (1)
_ = ↯

_ : send-msg-beta Sender Receiver 2 pk0 pk1 ≡ record { pk = pk0 ; msg-bit = 2 } -- expecting0 receive1 send curr byte (2)
_ = ↯

_ : send-msg-beta Sender Receiver 1 pk1 pk0 ≡ record { pk = pk1 ; msg-bit = 1 } -- expecting1 receive0 send curr byte (1)
_ = ↯

_ : send-msg-beta Sender Receiver 1 pk1 pk1 ≡ record { pk = pk0 ; msg-bit = 2 } -- expecting1 receive1 send next byte (2)
_ = ↯

_ : send-msg-beta Sender Receiver 25 pk0 pk0 ≡ record { pk = pk1 ; msg-bit = 26 } -- expecting1 receive1 send next byte (26)
_  = ↯

-------------------------------------------------------------------------------------------

r-a-t : ℕ → pk# → pk# → RAT
r-a-t msg-byte pk₁ pk₂ =
  let record { pk = pk′ ; msg-bit = msg-bit′ } = send-msg-beta {!!} {!!} msg-byte pk₁ pk₂
  in {!!}
  
r-a-t′ : send-sp-pkt-msg → RAT
r-a-t′ msg = {!!}
 

