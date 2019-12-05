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

send-sp-pkt′ : (expecting actual : pk#) → pk#
send-sp-pkt′ pk0 pk0 = pk1
send-sp-pkt′ pk0 pk1 = pk1
send-sp-pkt′ pk1 pk0 = pk0
send-sp-pkt′ pk1 pk1 = pk0

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
-- Receive ack or timeout. from sending message
r-a-t : ℕ → pk# → pk# → RAT
r-a-t msg-byte pk₁ pk₂ =
  let record { pk = pk′ ; msg-bit = msg-bit′ } = send-msg-beta Sender Receiver msg-byte pk₁ pk₂
  in r-ack
  
r-a-t′ : send-sp-pkt-msg → RAT
r-a-t′ msg = r-time


-------------------------------------------------------------------------------------------
-- Determine state of machine based off of r-a-t to use in the network
machinestate :  (node : principal) (recv-ack-timeout : RAT) → trans-state
machinestate node r-ack = ready
machinestate node r-time = waiting

_ : machinestate Sender (r-a-t 0 pk0 pk0) ≡ ready
_ = ↯

_ : machinestate Receiver (r-a-t 1 pk1 pk0) ≡ ready
_ = ↯

_ : machinestate Receiver (r-a-t′ (record { pk = pk0 ; msg-bit = 0 })) ≡ waiting
_ = ↯

_ : machinestate Sender (r-a-t′ (record { pk = pk0 ; msg-bit = 1 })) ≡ waiting
_ = ↯

_ : machinestate Sender (r-a-t 2 pk1 pk1)  ≡ ready
_ = ↯

_ : machinestate Sender r-ack ≡ ready
_ = ↯

_ : machinestate Sender r-time ≡ waiting
_ = ↯

_ : machinestate Receiver r-ack ≡ ready
_ = ↯

_ : machinestate Receiver r-time ≡ waiting
_ = ↯




--------------------------------------------------------------------------------------------
-- combine state of machine and sent packets.

-- # BASE CASE #
-- if the machine state is ready and node is sender (machine-state = ready) (left network)
--    then send the window frame bytes to receiver ((send pk#) to (right network))
--    switch sender (left network) to waiting state (sender = waiting)
-- ###########################################################################
-- # INDUCTIVE CASE #
-- # LEFT NETWORK (THE SENDER)
-- if the machine state is waiting and node is sender (Left network)
--    then wait for an ack or timeout (just check r-a-t ack or timeout)
--    move into ready state

--    if in ready state and had timeout (state = ready, and r-a-t = timeout)
--       resend pkts to receiver (send pk#)
--       go into waiting state  (state now = waiting)

--    if in ready state and received ACK  (state = ready, and r-a-t = ACK)
--       if ACK is expected   (ACK -> pk0 == pk0, or pk1==pk1)
--          then switch to next pkt to send (send pk#+1)
--          move into waiting state (state now = waiting)
--       if ACK is not expected  (ACK -> pk0 ≠ pk1 ∨ pk1 ≠ pk0)
--          resend window pkt   (send pk# (the previous packet that was just sent))
--          move into waiting state

--    if in ready state and nil (Should never happen wont be in proof)
--       move to waiting state  ( wont happen but state is now = waiting) {ensure state is returned to waiting}


-- # RIGHT NETWORK (THE RECEIVER)
-- if the machine state is waiting and the node is receiver (Right network)
--    then wait for pkts sent and msg-bit (check pk#)

--    if pkts match excpected
--       move to ready state and 
--       send a Success with ACK
--       move into waiting state

--    if the pkts do not match expected
--       move into ready state and
--       send previous received pkts (send expected ACK)
--       move to waiting state
-- ##########################################################################


-- if the machine state is waiting and the node is receiver (Right network)
--    then wait for pkts

-- if the machine state is ready and the received pkts are correct (send-msg-beta)
--    then Success

-- if the machine state is ready and received pkts are incorrect (send-msg-beta)
--    then Failure
--    send wait....  after waiting(r-time) sender will resend pkts that are correct (recursive call)


-- defining if then else methods!
-- first we want to decide what msg-byte to send to the next node
-- if the sent truth is true then send next byte
-- else send the byte we curr byte
mbit-if_then_else_ : 𝔹 → ℕ → ℕ → ℕ
mbit-if I then y else z = y
mbit-if O then y else z = z

-- check rat with bools
rat-if_then_else_ : 𝔹 → 𝔹 → 𝔹 → 𝔹
rat-if I then y else z = y
rat-if O then y else z = z

-- check state shift by rat
state-if_then_else_ : 𝔹 → RAT → RAT → RAT
state-if I then y else z = y
state-if O then y else z = z

-- check pkt send with pk#
pkt-if_then_else_ : 𝔹 → pk# → pk# → pk#
pkt-if I then y else z = y
pkt-if O then y else z = z

-- determine outcome of packets
-- if expecting ≠ actual then we have a bad receive
sent-truth : (pks pkr : pk#) → 𝔹
sent-truth pk0 pk0 = I
sent-truth pk0 pk1 = O
sent-truth pk1 pk0 = O
sent-truth pk1 pk1 = I

-- check if we had an ack/nak or timeout...
-- if sck we get a true value for above if
-- else: above if will be false
recv-ack-time : (ratr : RAT) → 𝔹
recv-ack-time r-ack = I
recv-ack-time r-time = O


record sent-pkt-bool : Set where
  field
    snt : 𝔹
    msg-bit : ℕ
    pkt-snt : pk#
    state : RAT

-- did not have time to incorporate the machine state as a function, so I just wrote the two options out.

state-msg-action : (state : trans-state) (curr-node dest-node : principal) (swindow rwindow : pk#) (msg-byte : ℕ) (rat : RAT) → sent-pkt-bool 

-- ready state sender  ignore rat -- we are just sending back to self or other network, this was handled in waiting 
state-msg-action ready Sender Sender swindow rwindow = λ msg-byte rat → record { snt = O ; msg-bit = 0 ; pkt-snt = swindow ; state = r-time }
state-msg-action ready Sender Receiver swindow rwindow msg-byte = λ rat →
  record { snt = sent-truth swindow rwindow ; msg-bit = mbit-if (sent-truth swindow rwindow) then (S msg-byte) else msg-byte ; pkt-snt = send-sp-pkt swindow rwindow ; state = r-ack } 


-- ready state receiver ignore rat
state-msg-action ready Receiver Receiver swindow rwindow = λ msg-byte rat → record { snt = O ; msg-bit = 0 ; pkt-snt = swindow ; state = r-time}
state-msg-action ready Receiver Sender swindow rwindow msg-byte = λ rat →
  record { snt = sent-truth swindow rwindow ; msg-bit = mbit-if (sent-truth swindow rwindow) then (S msg-byte) else msg-byte ; pkt-snt = send-sp-pkt′ swindow rwindow ; state = r-ack } 



-- waiting state sender use rat!
state-msg-action waiting Sender Sender swindow rwindow msg-byte rat  = record { snt = O ; msg-bit = msg-byte ; pkt-snt = swindow ; state = r-time}
state-msg-action waiting Sender Receiver swindow rwindow msg-byte rat = record { snt = rat-if (sent-truth swindow rwindow) ⩓ (recv-ack-time rat)
                                                                  then recv-ack-time r-ack else recv-ack-time r-time ; msg-bit = mbit-if ((sent-truth swindow rwindow) ⩓ recv-ack-time rat)
                                                                  then ((S msg-byte)) else msg-byte ; pkt-snt = pkt-if ((sent-truth swindow rwindow) ⩓ recv-ack-time rat)
                                                                  then (send-sp-pkt swindow rwindow) else rwindow ; state = state-if (recv-ack-time rat) then r-ack else r-time }


-- waiting state receiver use rat!
state-msg-action waiting Receiver Sender swindow rwindow msg-byte rat = record { snt = rat-if ((sent-truth swindow rwindow) ⩓ (recv-ack-time rat))
                                                                     then recv-ack-time r-ack else recv-ack-time r-time ; msg-bit = msg-byte ; pkt-snt = send-sp-pkt′ swindow rwindow ;
                                                                     state = state-if (recv-ack-time rat) then r-ack else r-time }
state-msg-action waiting Receiver Receiver swindow rwindow msg-byte rat = record { snt = O ; msg-bit = msg-byte ; pkt-snt = rwindow ; state = r-time }


-- test the waiting state need rat to determine if we are sending to ourself or to other network
_ : state-msg-action waiting Sender Receiver pk0 pk0 0 r-ack ≡ record { snt = I ; msg-bit = 1 ; pkt-snt = pk1 ; state = r-ack}
_ = ↯

_ : state-msg-action waiting Sender Receiver pk0 pk1 0 r-ack ≡ record { snt = O ; msg-bit = 0 ; pkt-snt = pk1 ; state = r-ack}
_ = ↯

_ : state-msg-action waiting Sender Sender pk0 pk0 0 r-time ≡ record { snt = O ; msg-bit = 0 ; pkt-snt = pk0 ; state = r-time}
_ = ↯

_ : state-msg-action waiting Receiver Receiver pk0 pk0 0 r-time ≡ record { snt = O ; msg-bit = 0 ; pkt-snt = pk0 ; state = r-time}
_ = ↯

_ : state-msg-action waiting Receiver Sender pk1 pk1 0  r-ack ≡ record { snt = I ; msg-bit = 0 ; pkt-snt = pk0 ; state = r-ack}
_ = ↯

_ : state-msg-action waiting Receiver Sender pk0 pk1 0 r-ack ≡ record { snt = O ; msg-bit = 0 ; pkt-snt = pk1 ; state = r-ack}
_ = ↯


-- test ready state ignoring rat here, it is not necessary

_ : state-msg-action ready Sender Receiver pk0 pk0 0 ≡ λ rat → record { snt = I ; msg-bit = 1 ; pkt-snt = pk1 }
_ = ↯

_ : state-msg-action ready Sender Receiver pk0 pk1 0 ≡ λ rat → record { snt = O ; msg-bit = 0 ; pkt-snt = pk0 }
_ = ↯

_ : state-msg-action ready Sender Sender pk0 pk0 ≡ λ msg-byte rat → record { snt = O ; msg-bit = 0 ; pkt-snt = pk0 }
_ = ↯

_ : state-msg-action ready Receiver Receiver pk0 pk0  ≡ λ  msg-byte rat → record { snt = O ; msg-bit = 0 ; pkt-snt = pk0 }
_ = ↯

_ : state-msg-action ready Receiver Sender pk1 pk1 0 ≡ λ rat → record { snt = I ; msg-bit = 1 ; pkt-snt = pk0 }
_ = ↯

_ : state-msg-action ready  Receiver Sender pk0 pk1 0 ≡ λ rat → record { snt = O ; msg-bit = 0 ; pkt-snt = pk1 }
_ = ↯


-- test a network flow

-- start sending pk0 to right network with msg-byte 35 with ack0
-- set machine to msg-byte 36 now, and expect pk1 and ack0
_ : state-msg-action ready Sender Receiver pk0 pk0 35 ≡ λ rat → record { snt = I ; msg-bit = S(35) ; pkt-snt = pk1 }
_ = ↯

--right network is waiting for pk0 and recvs pk0
-- set the machine to ready state
_ : state-msg-action waiting Receiver Sender pk0 pk0 36 r-ack ≡ record { snt = I ; msg-bit = 36 ; pkt-snt = pk1 ; state = r-ack }
_ = ↯
-- machine is prepared to send the nak0 back to the left network
-- send nak0 back to left network for conformation
_ : state-msg-action ready Receiver Sender pk0 pk0 36 ≡ λ rat → record { snt = I ; msg-bit = S(36) ; pkt-snt = pk1 }
_ = ↯


-- left network is still waiting for nak0
-- OH NO timeout!
-- machine to ready state, and set expected pk1 and sent next to false
-- shift back to expecting ack
_ : state-msg-action waiting Sender Receiver pk1 pk0 36 r-time ≡ record { snt = O ; msg-bit = 36 ; pkt-snt = pk0 ; state = r-time }
_ = ↯

-- machine will resend ack0 to right machine with 35 again
-- machine shifts into ready state
_ : state-msg-action ready Sender Receiver pk0 pk0 35 r-ack ≡ record { snt = I ; msg-bit = S(35) ; pkt-snt = pk1 ; state = r-ack }
_ = ↯

-- right machine still waiting for conformation about 36 received, but sees 35 again
-- handles any input and just returns back the same function
_ : state-msg-action waiting Receiver Sender pk0 pk0 36 r-ack ≡ record { snt = I ; msg-bit = 36 ; pkt-snt = pk1 ; state = r-ack }
_ = ↯
-- machine is prepared to send the nak0 back to the left network
-- send nak0 back to left network for conformation
_ : state-msg-action ready Receiver Sender pk0 pk0 36 ≡ λ rat → record { snt = I ; msg-bit = S(36) ; pkt-snt = pk1 }
_ = ↯


-- sender once again in waiting state looks for pk0 nak
-- shift to next window and send pk1 since pk0 was successful
-- switch to ready state
_ : state-msg-action waiting Sender Receiver pk0 pk0 36 r-ack ≡ record { snt = I ; msg-bit = S(36) ; pkt-snt = pk1 ; state = r-ack }
_ = ↯

-- send pk1 with next msg
-- move expected to 0 now
_ : state-msg-action ready Sender Receiver pk1 pk1 37 r-ack ≡ record { snt = I ; msg-bit = S(37) ; pkt-snt = pk0 ; state = r-ack }
_ = ↯

-- continues until entire message is received.

-- check pkt send with pk#
mstate-if_then_else_ : 𝔹 → trans-state → trans-state → trans-state
mstate-if I then y else z = y
mstate-if O then y else z = z

tot-if_then_else_ : 𝔹 → sent-pkt-bool → sent-pkt-bool → sent-pkt-bool
tot-if I then y else z = y
tot-if O then y else z = z

detmstate : RAT → 𝔹
detmstate r-ack = I
detmstate r-time = O


-- instead of defining all the machine states in the function I wanted to define machine state off of 
-- state-msg-action-beta : (state : trans-state) (curr-node dest-node : principal) (swindow rwindow : pk#) (msg-byte : ℕ) (rat : RAT) → sent-pkt-bool 

-- -- ready state sender  ignore rat -- we are just sending back to self or other network, this was handled in waiting
-- state-msg-action-beta state Receiver Receiver swindow rwindow msg-byte rat = tot-if detmstate rat
--   then {!!}
--   else {!!}
  
-- state-msg-action-beta state Sender Sender swindow rwindow msg-byte rat = tot-if detmstate rat
--   then {!!}
--   else {!!}

-- -- determine the two states
-- state-msg-action-beta state Sender Receiver swindow rwindow msg-byte rat = tot-if detmstate rat
--   then {!!}
--   else {!!}

-- -- determine the two states
-- state-msg-action-beta state Receiver Sender swindow rwindow msg-byte rat = tot-if detmstate rat
--   then {!!}
--   else {!!}
 
