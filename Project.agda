module Project where
open import Basics002

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
    SeqZer : pk#  -- Sequence number is either 0 
    SeqOne : pk#  -- 1


-- Define R-Ack or R-Timeout
data RAT : Set where
  r-ack : RAT
  r-time : RAT


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
infix 99 _seq-status_
data _seq-status_ : 𝔹 →  𝔹  → Set where
  SeqZeroZero : ∀{val1} → val1 seq-status val1
  SeqZeroOne : ∀{val1 val2} → val1 seq-status val2
  SeqOneZero : ∀{val1 val2} → val2 seq-status val1
  SeqOneOne : ∀{val2} → val2 seq-status val2


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
seq-state : (seq-stat-fst seq-stat-scnd : 𝔹) → (seq-stat-fst seq-status seq-stat-scnd)
seq-state O O = SeqZeroZero
seq-state O I = SeqZeroOne
seq-state I O = SeqOneZero
seq-state I I = SeqOneOne


_ : seq-state O O ≡ SeqZeroZero
_ = ↯

_ : seq-state O I ≡ SeqZeroOne
_ = ↯

_ : seq-state I O ≡ SeqOneZero
_ = ↯

_ : seq-state I I ≡ SeqOneOne
_ = ↯


get-seq : (window-send window-recv : pk#) → (Seq pk# pk#)
get-seq window-send  window-recv = window-send , window-recv

_ : get-seq pk0 pk0 ≡ sequence00
_ = ↯

_ : get-seq pk1 pk0 ≡ sequence10
_ = ↯

_ : get-seq pk0 pk1 ≡ sequence01
_ = ↯

_ : get-seq pk1 pk1 ≡ sequence11
_ = ↯


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
-- Receive ack or timeout.
r-a-t : ℕ → pk# → pk# → RAT
r-a-t msg-byte pk₁ pk₂ =
  let record { pk = pk′ ; msg-bit = msg-bit′ } = send-msg-beta Sender Receiver msg-byte pk₁ pk₂
  in r-ack
  
r-a-t′ : send-sp-pkt-msg → RAT
r-a-t′ msg = r-time


-------------------------------------------------------------------------------------------
-- Determine state of machine
machinestate :  (node : principal) (recv-ack-timeout : RAT) → trans-state
machinestate node r-ack = ready
machinestate node r-time = waiting

_ : machinestate Sender (r-a-t 0 pk0 pk0) ≡ ready
_ = ↯

_ : machinestate Receiver (r-a-t 1 pk1 pk0) ≡ ready
_ = ↯

_ : machinestate Receiver (r-a-t′ (record { pk = pk0 ; msg-bit = 0 })) ≡ waiting
_ = ↯

_ : machinestate Sender r-ack ≡ ready
_ = ↯

_ : machinestate Sender r-time ≡ waiting
_ = ↯

_ : machinestate Receiver r-ack ≡ ready
_ = ↯

_ : machinestate Receiver r-time ≡ waiting
_ = ↯



 

