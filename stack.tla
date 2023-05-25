------------------------------- MODULE stack -------------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS Readers, Writers, MsgCount
(*--fair algorithm LFStack{
\* The first element of stask is 0 to indicate end of stask.
\* Later stask will be appended with incremented Idx, therefore other 0 in stask.
variables main_stack = <<0>>,
          StackTop = 0,
         MsgRead = 0,
         Idx = 0,
         Msgs = MsgCount,
         RcvdMsgs = {};

define {
\* Correctness
  AllWasRecieved == <>(\A n \in 1..MsgCount : n \in RcvdMsgs)
  NoOtherMsgsRecieved == [](\A n \in RcvdMsgs : n \in 1..MsgCount)
};
macro CAS(success, ptr, old, new) {
    if (ptr = old){
        ptr := new;
        success := TRUE;
    }
    else
        success := FALSE;
}

procedure push(new_elt)
variables top = 0, Succ = FALSE;
{
    push_loop: while(TRUE) {
        read_top: top:= StackTop;
        rewrite: CAS(Succ, StackTop, top, top+1);
        if(Succ) {
            main_stack := <<new_elt>> \o main_stack;
            push_ret: return;
        }
    };
}

procedure pop()
variables top = 0, Succ = FALSE;
{
    pop_loop: while(TRUE) {
        read_top: top := StackTop;
        if(top = 0){
          RcvInfo := -1;
          fail: return;
        };
        rewrite: CAS(Succ, StackTop, top, top-1);
        if(Succ) {
            RcvInfo := Head(main_stack);
            main_stack := Tail(main_stack);
            pop_ret: return;
        }

    };
}


process (s \in Readers)
variables SendInfo = -1;
{

  push_loop: while(Msgs > 0){
     get_message: SendInfo := Msgs;
     Msgs := Msgs - 1;
     check_msg: if(SendInfo > 0){
       perform_push: call push(SendInfo)
     }
  }
}

process (r \in Writers)
variable RcvInfo = -1;
{
  pop_loop: while(MsgRead < MsgCount){
     await Len(main_stack) > 1;
     perform_pop: call pop();
     \* Increment only if popped successfully
     increment_rcv: if(RcvInfo /= -1){
       MsgRead := MsgRead + 1;
       assert(~(RcvInfo \in RcvdMsgs));
       RcvdMsgs := RcvdMsgs \union {RcvInfo};
     }
  }
}

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "5781d0c2" /\ chksum(tla) = "90f024e0")
\* Label push_loop of procedure push at line 32 col 16 changed to push_loop_
\* Label read_top of procedure push at line 33 col 19 changed to read_top_
\* Label rewrite of procedure push at line 21 col 5 changed to rewrite_
\* Label pop_loop of procedure pop at line 45 col 15 changed to pop_loop_
\* Procedure variable top of procedure push at line 30 col 11 changed to top_
\* Procedure variable Succ of procedure push at line 30 col 20 changed to Succ_
CONSTANT defaultInitValue
VARIABLES main_stack, StackTop, MsgRead, Idx, Msgs, RcvdMsgs, pc, stack

(* define statement *)
AllWasRecieved == <>(\A n \in 1..MsgCount : n \in RcvdMsgs)
NoOtherMsgsRecieved == [](\A n \in RcvdMsgs : n \in 1..MsgCount)

VARIABLES new_elt, top_, Succ_, top, Succ, SendInfo, RcvInfo

vars == << main_stack, StackTop, MsgRead, Idx, Msgs, RcvdMsgs, pc, stack,
           new_elt, top_, Succ_, top, Succ, SendInfo, RcvInfo >>

ProcSet == (Readers) \cup (Writers)

Init == (* Global variables *)
        /\ main_stack = <<0>>
        /\ StackTop = 0
        /\ MsgRead = 0
        /\ Idx = 0
        /\ Msgs = MsgCount
        /\ RcvdMsgs = {}
        (* Procedure push *)
        /\ new_elt = [ self \in ProcSet |-> defaultInitValue]
        /\ top_ = [ self \in ProcSet |-> 0]
        /\ Succ_ = [ self \in ProcSet |-> FALSE]
        (* Procedure pop *)
        /\ top = [ self \in ProcSet |-> 0]
        /\ Succ = [ self \in ProcSet |-> FALSE]
        (* Process s *)
        /\ SendInfo = [self \in Readers |-> -1]
        (* Process r *)
        /\ RcvInfo = [self \in Writers |-> -1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Readers -> "push_loop"
                                        [] self \in Writers -> "pop_loop"]

push_loop_(self) == /\ pc[self] = "push_loop_"
                    /\ pc' = [pc EXCEPT ![self] = "read_top_"]
                    /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                    RcvdMsgs, stack, new_elt, top_, Succ_, top,
                                    Succ, SendInfo, RcvInfo >>

read_top_(self) == /\ pc[self] = "read_top_"
                   /\ top_' = [top_ EXCEPT ![self] = StackTop]
                   /\ pc' = [pc EXCEPT ![self] = "rewrite_"]
                   /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                   RcvdMsgs, stack, new_elt, Succ_, top, Succ,
                                   SendInfo, RcvInfo >>

rewrite_(self) == /\ pc[self] = "rewrite_"
                  /\ IF StackTop = top_[self]
                        THEN /\ StackTop' = top_[self]+1
                             /\ Succ_' = [Succ_ EXCEPT ![self] = TRUE]
                        ELSE /\ Succ_' = [Succ_ EXCEPT ![self] = FALSE]
                             /\ UNCHANGED StackTop
                  /\ IF Succ_'[self]
                        THEN /\ main_stack' = <<new_elt[self]>> \o main_stack
                             /\ pc' = [pc EXCEPT ![self] = "push_ret"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "push_loop_"]
                             /\ UNCHANGED main_stack
                  /\ UNCHANGED << MsgRead, Idx, Msgs, RcvdMsgs, stack, new_elt,
                                  top_, top, Succ, SendInfo, RcvInfo >>

push_ret(self) == /\ pc[self] = "push_ret"
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ top_' = [top_ EXCEPT ![self] = Head(stack[self]).top_]
                  /\ Succ_' = [Succ_ EXCEPT ![self] = Head(stack[self]).Succ_]
                  /\ new_elt' = [new_elt EXCEPT ![self] = Head(stack[self]).new_elt]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                  RcvdMsgs, top, Succ, SendInfo, RcvInfo >>

push(self) == push_loop_(self) \/ read_top_(self) \/ rewrite_(self)
                 \/ push_ret(self)

pop_loop_(self) == /\ pc[self] = "pop_loop_"
                   /\ pc' = [pc EXCEPT ![self] = "read_top"]
                   /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                   RcvdMsgs, stack, new_elt, top_, Succ_, top,
                                   Succ, SendInfo, RcvInfo >>

read_top(self) == /\ pc[self] = "read_top"
                  /\ top' = [top EXCEPT ![self] = StackTop]
                  /\ IF top'[self] = 0
                        THEN /\ RcvInfo' = [RcvInfo EXCEPT ![self] = -1]
                             /\ pc' = [pc EXCEPT ![self] = "fail"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "rewrite"]
                             /\ UNCHANGED RcvInfo
                  /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                  RcvdMsgs, stack, new_elt, top_, Succ_, Succ,
                                  SendInfo >>

fail(self) == /\ pc[self] = "fail"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ top' = [top EXCEPT ![self] = Head(stack[self]).top]
              /\ Succ' = [Succ EXCEPT ![self] = Head(stack[self]).Succ]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                              RcvdMsgs, new_elt, top_, Succ_, SendInfo,
                              RcvInfo >>

rewrite(self) == /\ pc[self] = "rewrite"
                 /\ IF StackTop = top[self]
                       THEN /\ StackTop' = top[self]-1
                            /\ Succ' = [Succ EXCEPT ![self] = TRUE]
                       ELSE /\ Succ' = [Succ EXCEPT ![self] = FALSE]
                            /\ UNCHANGED StackTop
                 /\ IF Succ'[self]
                       THEN /\ RcvInfo' = [RcvInfo EXCEPT ![self] = Head(main_stack)]
                            /\ main_stack' = Tail(main_stack)
                            /\ pc' = [pc EXCEPT ![self] = "pop_ret"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "pop_loop_"]
                            /\ UNCHANGED << main_stack, RcvInfo >>
                 /\ UNCHANGED << MsgRead, Idx, Msgs, RcvdMsgs, stack, new_elt,
                                 top_, Succ_, top, SendInfo >>

pop_ret(self) == /\ pc[self] = "pop_ret"
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ top' = [top EXCEPT ![self] = Head(stack[self]).top]
                 /\ Succ' = [Succ EXCEPT ![self] = Head(stack[self]).Succ]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                 RcvdMsgs, new_elt, top_, Succ_, SendInfo,
                                 RcvInfo >>

pop(self) == pop_loop_(self) \/ read_top(self) \/ fail(self)
                \/ rewrite(self) \/ pop_ret(self)

push_loop(self) == /\ pc[self] = "push_loop"
                   /\ IF Msgs > 0
                         THEN /\ pc' = [pc EXCEPT ![self] = "get_message"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                   RcvdMsgs, stack, new_elt, top_, Succ_, top,
                                   Succ, SendInfo, RcvInfo >>

get_message(self) == /\ pc[self] = "get_message"
                     /\ SendInfo' = [SendInfo EXCEPT ![self] = Msgs]
                     /\ Msgs' = Msgs - 1
                     /\ pc' = [pc EXCEPT ![self] = "check_msg"]
                     /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx,
                                     RcvdMsgs, stack, new_elt, top_, Succ_,
                                     top, Succ, RcvInfo >>

check_msg(self) == /\ pc[self] = "check_msg"
                   /\ IF SendInfo[self] > 0
                         THEN /\ pc' = [pc EXCEPT ![self] = "perform_push"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "push_loop"]
                   /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                   RcvdMsgs, stack, new_elt, top_, Succ_, top,
                                   Succ, SendInfo, RcvInfo >>

perform_push(self) == /\ pc[self] = "perform_push"
                      /\ /\ new_elt' = [new_elt EXCEPT ![self] = SendInfo[self]]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "push",
                                                                  pc        |->  "push_loop",
                                                                  top_      |->  top_[self],
                                                                  Succ_     |->  Succ_[self],
                                                                  new_elt   |->  new_elt[self] ] >>
                                                              \o stack[self]]
                      /\ top_' = [top_ EXCEPT ![self] = 0]
                      /\ Succ_' = [Succ_ EXCEPT ![self] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = "push_loop_"]
                      /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                      RcvdMsgs, top, Succ, SendInfo, RcvInfo >>

s(self) == push_loop(self) \/ get_message(self) \/ check_msg(self)
              \/ perform_push(self)

pop_loop(self) == /\ pc[self] = "pop_loop"
                  /\ IF MsgRead < MsgCount
                        THEN /\ Len(main_stack) > 1
                             /\ pc' = [pc EXCEPT ![self] = "perform_pop"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                  RcvdMsgs, stack, new_elt, top_, Succ_, top,
                                  Succ, SendInfo, RcvInfo >>

perform_pop(self) == /\ pc[self] = "perform_pop"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pop",
                                                              pc        |->  "increment_rcv",
                                                              top       |->  top[self],
                                                              Succ      |->  Succ[self] ] >>
                                                          \o stack[self]]
                     /\ top' = [top EXCEPT ![self] = 0]
                     /\ Succ' = [Succ EXCEPT ![self] = FALSE]
                     /\ pc' = [pc EXCEPT ![self] = "pop_loop_"]
                     /\ UNCHANGED << main_stack, StackTop, MsgRead, Idx, Msgs,
                                     RcvdMsgs, new_elt, top_, Succ_, SendInfo,
                                     RcvInfo >>

increment_rcv(self) == /\ pc[self] = "increment_rcv"
                       /\ IF RcvInfo[self] /= -1
                             THEN /\ MsgRead' = MsgRead + 1
                                  /\ Assert((~(RcvInfo[self] \in RcvdMsgs)),
                                            "Failure of assertion at line 84, column 8.")
                                  /\ RcvdMsgs' = (RcvdMsgs \union {RcvInfo[self]})
                             ELSE /\ TRUE
                                  /\ UNCHANGED << MsgRead, RcvdMsgs >>
                       /\ pc' = [pc EXCEPT ![self] = "pop_loop"]
                       /\ UNCHANGED << main_stack, StackTop, Idx, Msgs, stack,
                                       new_elt, top_, Succ_, top, Succ,
                                       SendInfo, RcvInfo >>

r(self) == pop_loop(self) \/ perform_pop(self) \/ increment_rcv(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: push(self) \/ pop(self))
           \/ (\E self \in Readers: s(self))
           \/ (\E self \in Writers: r(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu May 25 04:15:44 MSK 2023 by denist
\* Created Thu May 24 19:45:32 MSK 2023 by denist
