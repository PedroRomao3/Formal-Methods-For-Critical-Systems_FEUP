
--===============================================
-- M.EIC037: Formal Methods for Critical Systems
-- 2024/2025
--
-- Mini Project 1
--
-- Group Members:  José Felisberto, 202108657
--                 Bruno Machado, 201907715
--                 Pedro Romão, 202108860 
--                  
--
--===============================================

enum Status {External, Fresh, Active, Purged}

abstract sig Object {}

abstract sig Boolean {}
one sig True, False extends Boolean {}

sig Message extends Object {
  var status: lone Status,
  var read: lone Boolean
}

sig Mailbox extends Object {
  var messages: set Message  
}

-- Mail application
one sig Mail {
  -- system mailboxes
  inbox: Mailbox,
  drafts: Mailbox,
  trash: Mailbox,
  sent: Mailbox,
  -- user mailboxes
  var uboxes: set Mailbox,

  var op: lone Operator -- added for tracking purposes only
}

-- added for convenience, to track the operators applied during 
-- a system execution 
enum Operator {CMB, DMB, CM, GM, SM, DM, MM, ET, RM}

-- Since we have only one Mail app, it is convenient to have
-- a global shorthand for its system mailboxes
fun sboxes : set Mailbox { Mail.inbox + Mail.drafts + Mail.trash + Mail.sent }

------------------------------
-- Improvements
------------------------------
fact ValidStatusTransitions {
  always (
    all m: Message |
      // Fresh can only become Active
      (m.status = Fresh and m.status' != Fresh) => m.status' = Active
      and
      // External can only become Active
      (m.status = External and m.status' != External) => m.status' = Active
      and
      // Active can only become Purged
      (m.status = Active and m.status' != Active) => m.status' = Purged
      and
      // Purged stays Purged
      (m.status = Purged) => m.status' = Purged
  )
}


------------------------------
-- Frame condition predicates
------------------------------

-- You can use these predicates in the definition of the operators

-- the status of the messages in M is unchanged from a state to the next
pred noStatusChange [M: set Message] {
  all m: M | m.status' = m.status
}

-- the set of messages in each mailbox in MB is unchanged from a state to the next
pred noMessageChange [MB: set Mailbox] {
  all mb: MB | mb.messages' = mb.messages
}

-- the set of user-defined mailboxes is unchanged from a state to the next
pred noUserboxChange {
  Mail.uboxes' = Mail.uboxes
}

pred noReadChange [M: set Message] {
  all m: M | m.read' = m.read
}

-------------
-- Operators
-------------


/* Leave the constraint on Mail.op' in the operators.
   It is there to track the applied operators in each trace  
*/


pred createMessage[m: Message] {
    // --- Preconditions ---
    // The message must be fresh (not in any mailbox)
    m.status = Fresh

    // --- Postconditions ---
    // The new message is added to the drafts mailbox
    m in Mail.drafts.messages'

    // The message status is set to Active
    m.status' = Active

    // --- Frame Conditions ---
    // Other mailboxes remain unchanged
    noMessageChange[Mailbox - Mail.drafts]

    // The status of other messages remains unchanged
    noStatusChange[Message - m]

    // Other mail structure stays the same
    noUserboxChange

    // Operation tracking reflects this as a createMessage operation
    Mail.op' = CM
}

pred moveMessage[m: Message, dst: Mailbox] {
  
  // --- Preconditions ---
  // Message must be active
  m.status = Active
  dst != Mail.trash

  // Message must be in a source mailbox
  some src: Mailbox - Mail.trash | {
    m in src.messages
    dst != src
    

    // --- Postconditions ---
    // Message moves from src to dst
    m in dst.messages'
    m not in src.messages'

    // --- Frame Conditions ---
    noStatusChange[Message]  // Other messages' status remains unchanged
    noMessageChange[Mailbox - src - dst]  // Other mailboxes remain unchanged
    noUserboxChange  // User-created mailboxes remain unchanged
    Mail.op' = MM

  }
}




-- deleteMessage
pred deleteMessage[msg: Message] {
    
    

    // --- Preconditions ---
    // The message must be in a mailbox other than trash and be active
    msg.status = Active
    some mb: Mailbox - Mail.trash | msg in mb.messages

    // --- Postconditions ---
    // The message is removed from its original mailbox and added to trash
    msg in Mail.trash.messages'
    all mb: Mailbox - Mail.trash | 
        msg in mb.messages => msg not in mb.messages'

    // --- Frame Conditions ---
    noStatusChange[Message]  // msg and Other messages’ status remains unchanged
    let unaffectedMailboxes = Mail.uboxes + sboxes - (Mailbox & msg.~messages) |
        noMessageChange[unaffectedMailboxes]  // Other mailbox contents unchanged
    Mail.op' = DM

}



-- sendMessage
pred sendMessage[msg: Message] {
    
    

    // --- Preconditions ---
    msg in Mail.drafts.messages
    msg.status = Active

    // --- Postconditions ---
    msg in Mail.sent.messages'
    msg not in Mail.drafts.messages'

    // --- Frame Conditions ---
    noStatusChange[Message]  

    let unaffectedMailboxes = Mailbox - Mail.sent - Mail.drafts |
      noMessageChange[unaffectedMailboxes]

    Mail.op' = SM
}

pred getMessage[m: Message] {
    
    

    // --- Preconditions ---
    m not in Mail.inbox.messages
    m.status = External

    // --- Postconditions ---
    m in Mail.inbox.messages'
    m.status' = Active


    // --- Frame Conditions ---
    noStatusChange[Message - m]

    noMessageChange[Mailbox - Mail.inbox]

    Mail.op' = GM
}

pred emptyTrash {
    
    

    // --- Preconditions ---
    some m: Message | m in Mail.trash.messages

    // --- Postconditions ---
    Mail.trash.messages' = none

    all m: Message | m in Mail.trash.messages => m.status' = Purged
    all m: Message | m in Mail.trash.messages => m.read' = m.read

    // --- Frame Conditions ---
    noStatusChange[Message - Mail.trash.messages]

    noMessageChange[Mailbox - Mail.trash]
    Mail.op' = ET
}

pred createMailbox [mb: Mailbox] {
    
    

    // --- Preconditions ---
    mb not in Mail.uboxes
    mb not in sboxes
    mb.messages = none

    // --- Postconditions ---
    Mail.uboxes' = Mail.uboxes + mb
    mb.messages' = none

    all m: Message | m not in mb.messages'
    

    // --- Frame Conditions ---
    noStatusChange[Message]
    noMessageChange[Mailbox - mb]
    Mail.op' = CMB
}

pred deleteMailbox [mb: Mailbox] {
    

    // --- Preconditions ---
    mb in Mail.uboxes
    mb not in sboxes

    // --- Postconditions ---
    all m: Message | m in mb.messages => m.status' = Purged
    all m: Message | m in mb.messages => m.read' = m.read
    mb.messages' = none
    Mail.uboxes' = (Mail.uboxes - mb)

    // --- Frame Conditions ---
    noStatusChange[Message - mb.messages]

    noMessageChange[Mailbox - mb]
    Mail.op' = DMB
}

pred readMessage[m: Message] {
    // --- Preconditions ---
    m.status = Active  
    m.read = False  
    some mb: Mailbox | m in mb.messages  
    
    // --- Postconditions ---
    m.read' = True  // Message becomes read
    
    // --- Frame Conditions ---
    noStatusChange[Message]  // Status remains unchanged
    noMessageChange[Mailbox]  // Message locations remain unchanged
    noUserboxChange  // User-created mailboxes remain unchanged
    all msg: Message - m | msg.read' = msg.read  // Other messages' read status remains unchanged
    Mail.op' = RM  // Set the operator
}

pred noOp {
    
    

    // --- Preconditions ---
    // No conditions; we simply preserve the current state.

    // --- Postconditions ---
    all mb: Mailbox | mb'.messages = mb.messages
    all m: Message | m'.status = m.status
    all m: Message | m'.read = m.read

    // --- Frame Conditions ---
    Mail.op' = none

}

pred Init {
    // --- Initial Conditions ---
    all m: Message | m.status = Fresh
    all m: Message | m.read = False

    // The system mailboxes are all distinct
    #sboxes = 4
    

    // All mailboxes anywhere are empty
    all mb: Mailbox | no mb.messages

    // The set of user-created mailboxes is empty
    no Mail.uboxes

    // No operator generates the initial state
    Mail.op = none
}



------------------------
-- Transition predicate
------------------------

pred Trans {
  (some mb: Mailbox | createMailbox [mb])
  or
  (some mb: Mailbox | deleteMailbox [mb])
  or
  (some m: Message | createMessage [m])
  or  
  (some m: Message | getMessage [m])
  or
  (some m: Message | sendMessage [m])
  or   
  (some m: Message | deleteMessage [m])
  or 
  (some m: Message | some mb: Mailbox | moveMessage [m, mb])
  or
  (some m: Message | readMessage [m])
  or 
  emptyTrash
  or 
  noOp
}


----------
-- Traces
----------

-- Restricts the set of traces to all and only the executions of the Mail app

fact System {
  -- traces must satisfy initial state condition and the transition condition
  Init and always Trans
}


run {} for 10

---------------------
-- Sanity check runs
---------------------

pred p1 {
  -- Eventually a message becomes active
  eventually {
        some m: Message | m.status = Active
    }
}
run p1 for 1 but 8 Object

pred p2 {
  -- The inbox contains more than one message at some point
  eventually {
        #(Mail.inbox.messages) > 1
    }
}
run p2 for 1 but 8 Object

pred p3 {
  -- The trash mailbox eventually contains messages and
  -- becomes empty some time later
  eventually {
    some t: Message | t in Mail.trash.messages &&
    eventually {
      Mail.trash.messages = none
    }
  }
}
run p3 for 1 but 8 Object

pred p4 {
  -- Eventually some message in the drafts mailbox (it is already there) moves to the sent mailbox
  eventually {
    some m: Message | m in Mail.drafts.messages && 
    eventually {
      m in Mail.sent.messages
    }
  }
}
// eventually {
//     some m: Message | m in Mail.sent.messages and once (m in Mail.drafts.messages)
//   }
run p4 for 1 but 8 Object

pred p5 {
  -- Eventually there is a user mailbox with messages in it
  eventually {
    some mb: Mail.uboxes | some m: Message | m in mb.messages
  }
}
run p5 for 1 but 8 Object 

pred p6 {
  -- Eventually the inbox gets two messages in a row from outside
  eventually {
    -- Two consecutive getMessage operations
    Mail.op = GM and Mail.op' = GM
    
    some m1, m2: Message | {
      -- Before state: both messages were external and not in inbox
      before {
        m1.status = External and m2.status = External and
        m1 not in Mail.inbox.messages and m2 not in Mail.inbox.messages
      }
      
      -- Current state: m1 just arrived, m2 still waiting
      m1.status = Active and m1 in Mail.inbox.messages and
      m2.status = External and m2 not in Mail.inbox.messages
      
      -- Next state: m2 arrives right after m1
      m1.status' = Active and m1 in Mail.inbox.messages' and
      m2.status' = Active and m2 in Mail.inbox.messages'
    }
  }
}

run p6 for 1 but 8 Object

pred p7 {
  -- Eventually some user mailbox gets deleted
  eventually {
    Mail.op' = DMB
    some mb: Mail.uboxes | mb not in Mail.uboxes'
}
}

run p7 for 1 but 8 Object

pred p8 {
  -- Eventually the inbox has messages
  eventually {
    some m: Message | m in Mail.inbox.messages
  }
  
  -- Every message that enters the inbox is eventually removed (not necessarily immediately)
  all m: Message |
    always (m in Mail.inbox.messages => eventually (m not in Mail.inbox.messages))
}
run p8 for 1 but 8 Object

pred p9 {
  -- The trash mail box is emptied of its messages eventually
  eventually {
        Mail.op = ET
        Mail.trash.messages = none
    }
}
run p9 for 1 but 8 Object

pred p10 {
  -- Eventually an external message arrives and
  -- after that nothing happens anymore
  eventually {
    some m: Message | {
      -- A message just arrived (the getMessage operation happened)
      Mail.op = GM and
      
      -- Current state: message is now active in inbox
      m.status = Active and
      m in Mail.inbox.messages and
      
      -- Previously this message was external
      before (m.status = External and m not in Mail.inbox.messages) and
      
      -- From that point forward, only noOp occurs
      after always (Mail.op = none)
    }
  }
}
run p10 for 1 but 8 Object

pred readMessageWorks {
  eventually {
    some m: Message | m.read = True
  }
}
run readMessageWorks for 5 but 11 Object

--------------------
-- Valid Properties
--------------------

assert v1 {
--  Every active message is in one of the app's mailboxes 
  all m: Message |
    m.status = Active =>
    some mb: Mailbox | m in mb.messages
}
check v1 for 5 but 11 Object

assert v2 {
--  Inactive messages are in no mailboxes at all
  all m: Message |
    m.status != Active =>
    all mb: Mailbox | m not in mb.messages
}
check v2 for 5 but 11 Object

assert v3 {
-- Each of the user-created mailboxes differs from the predefined mailboxes
  all mb: Mail.uboxes |
    mb != Mail.inbox and mb != Mail.drafts and mb != Mail.trash and mb != Mail.sent

}
check v3 for 5 but 11 Object

assert v4 {
-- Every active message was once external or fresh.
  all m: Message |
    m.status = Active =>
    once (m.status = External or m.status = Fresh)

}
check v4 for 5 but 11 Object

assert v5 {
  -- Every mailbox is empty when first added to uboxes
  all mb: Mailbox - sboxes|
    always (
      (mb not in Mail.uboxes and mb in Mail'.uboxes) => 
      (no mb.messages and no mb.messages')
    )
}
check v5 for 5 but 11 Object

assert v6 {
  -- User-created mailboxes stay in the system's uboxes set until explicitly deleted
  all mb: Mailbox |
    once (mb in Mail.uboxes) =>
      always (mb in Mail.uboxes or once (Mail.op = DMB and mb not in Mail.uboxes'))
}
check v6 for 5 but 11 Object

assert v7 {
-- Every sent message is sent from the draft mailbox 
  all m: Message |
    m in Mail.sent.messages =>
    once (m in Mail.drafts.messages)
}
check v7 for 5 but 11 Object

assert v8 {
-- The app's mailboxes contain only active messages
  all mb: Mailbox, m: Message |
    m in mb.messages => m.status = Active
}
check v8 for 5 but 11 Object

assert v9 {
-- Every received message passes through the inbox
  all m: Message |
    (some mb: Mailbox | m in mb.messages) =>
    once (m in Mail.inbox.messages)
}
check v9 for 5 but 11 Object

assert v10 {
-- A purged message is purged forever
  all m: Message |
    once (m.status = Purged) => always (m.status = Purged)

}
check v10 for 5 but 11 Object

assert v11 {
-- No messages in the system can ever (re)acquire External status
  all m: Message | m.status = External =>
    once (m.status != External) => 
    always (m.status != External)
}
check v11 for 5 but 11 Object

assert v12 {
-- The trash mailbox starts empty and stays so until a message is deleted, if any

  -- Trash is empty initially
  no Mail.trash.messages

  -- If something appears in trash, it must have been deleted there later
  all m: Message |
    once (m in Mail.trash.messages) =>
    once (some mb: Mailbox - Mail.trash | m in mb.messages)
}
check v12 for 5 but 11 Object

assert v13 {
-- To purge an active message one must first delete the message 
-- or delete the mailbox it is in.
  all m: Message |
    (once m.status = Active and m.status = Purged) =>
    once (m in Mail.trash.messages or some mb: Mailbox | m in mb.messages and mb not in Mailbox)
}
check v13 for 5 but 11 Object

assert v14 {
-- Every message in the trash mailbox had been previously deleted
  all m: Message |
    m in Mail.trash.messages =>
    once (some mb: Mailbox - Mail.trash | m in mb.messages)
}
check v14 for 5 but 11 Object

assert v15 {
-- Every message in a user-created mailbox ultimately comes from a system mailbox.
  all m: Message |
    ( some mb: Mail.uboxes | m in mb.messages)  =>
    once (some sys: Mailbox | sys in sboxes and m in sys.messages)
}
check v15 for 5 but 11 Object

assert v16 {
  -- A purged message that was never in the trash mailbox must have been 
  -- in a user mailbox that was later deleted
  all m: Message |
    m.status = Purged and not once (m in Mail.trash.messages) =>
    some mb: Mailbox | once (
      mb in Mail.uboxes and        
      m in mb.messages and       
      eventually (                
        Mail.op = DMB and         
        mb not in Mail.uboxes'     
      )
    )
}
check v16 for 5 but 11 Object


----------------------
-- Invalid Properties
----------------------

-- It is possible for messages to stay in the inbox indefinitely
-- Negation into: Every message that enters the inbox must eventually leave the inbox.
assert i1 {
  all m: Message |
    always (m in Mail.inbox.messages implies eventually (m not in Mail.inbox.messages))
}
check i1 for 5 but 11 Object

-- A message that was removed from the inbox may later reappear there.
-- Negation into: A message that was once in the inbox and later removed never reappears there.
assert i2 {
  all m: Message |
    always ((once m in Mail.inbox.messages and not (m in Mail.inbox.messages)) implies always (m not in Mail.inbox.messages))
}
check i2 for 5 but 11 Object

-- A deleted message may go back to the mailbox it was deleted from.
-- Negated into: No message that was once in a mailbox and later deleted can reappear in that mailbox.
assert i3 {
all m: Message, mb: Mailbox |
    always (
      (once m in mb.messages and not (m in mb.messages)) implies
      always (m not in mb.messages)
    )
}
check i3 for 5 but 11 Object


-- Some external messages may never be received
-- Negation into: AEvery external message eventually stops being external.
assert i4 {
  all m: Message |
    always (m.status = External implies eventually (m.status != External and m in Mail.inbox.messages))
}
check i4 for 5 but 11 Object


assert readPersistence {
  -- Once a message is read, it stays read until purged
  all m: Message |
    once (m.read = True) => 
    always (m.read = True)
}
check readPersistence for 5 but 11 Object
