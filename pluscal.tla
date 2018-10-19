--------------------------- MODULE pluscal ----------------------------
(* Lamport's mutual-exclusion algorithm in PlusCal. *)

EXTENDS Naturals, Sequences
CONSTANT N, maxClock

(* N nodes execute the algorithm. Each node is represented by two processes:
   the main "site" that requests access to the critical section, and a
   "communicator" that asynchronously receives messages directed to the "site"
   and updates the data structure. Unfortunately, PlusCal does not have
   nested processes, so we have to model sites and communicators as top-level
   processes. Sites are numbered from 1 to N, communicators from N+1 to 2N.

   The constant maxClock is used to bound the state space explored by the
   model checker, see predicate ClockConstraint below.
*)

Sites == 1 .. N
Comms == N+1 .. 2*N
site(c) == c - N   (* site a communicator is acting for *)
max(x,y) == IF x < y THEN y ELSE x

(* --algorithm LamportMutex
       variables
         (* two-dimensional array of message queues: enforce FIFO order
            between any pair of processes *)
         network = [from \in Sites |-> [to \in Sites |-> << >> ]];
         (* logical clock per site, initialized to 1 *)
         clock = [s \in Sites |-> 1];
         (* queue of pending requests per process, ordered by logical clock;
            entries are records of the form [site |-> s, clk |-> c] where
            the clock value c is non-zero *)
         reqQ = [s \in Sites |-> << >>];
         (* set of processes who sent acknowledgements for own request *)
         acks = [s \in Sites |-> {}];

       define 
         (* check if request rq1 has higher priority than rq2 according to
            time stamp: both requests are records as they occur in reqQ *)
         beats(rq1, rq2) == 
           \/ rq1.clk < rq2.clk
           \/ rq1.clk = rq2.clk /\ rq1.site < rq2.site

         (* Compute the network obtained from net by sending message "msg" from
            site "from" to site "to".
            NB: Use a definition rather than a macro because this allows us to
                have multiple changes to the network in a single atomic step
                (rather kludgy, though).
         *)
         send(net, from, to, msg) == 
           [net EXCEPT ![from][to] = Append(@, msg)]

         (* Compute the network obtained from net by broadcasting message "msg"
            from site "from" to all sites. *)
         broadcast(net, from, msg) ==
           [net EXCEPT ![from] = [to \in Sites |-> Append(net[from][to], msg)]]
       end define;

       (* insert a request from site from in reqQ of site s *)
       macro insertRequest(s, from, clk)
       begin
         with entry = [site |-> from, clk |-> clk],
              len = Len(reqQ[s]),
              pos = CHOOSE i \in 1 .. len + 1 :
                        /\ \A j \in 1 .. i-1 : beats(reqQ[s][j], entry)
                        /\ \/ i = len + 1
                           \/ beats(entry, reqQ[s][i])
         do
           reqQ[s] := SubSeq(reqQ[s], 1, pos-1) \circ << entry >>
                      \circ SubSeq(reqQ[s], pos, len);
         end with;
       end macro;

       (* remove a request from site from in reqQ of site s --
          assume that there is at most one such request in the queue *)
       macro removeRequest(s, from)
       begin
         with len = Len(reqQ[s]),
              pos = CHOOSE i \in 1 .. len : reqQ[s][i].site = from
         do
           if (reqQ[s][pos].site = from)
           then
              (* request actually exists *)
              reqQ[s] := SubSeq(reqQ[s], 1, pos-1) \circ SubSeq(reqQ[s], pos+1, len);
           end if;
         end with;
       end macro;

       process Site \in Sites
       begin
         start:
           while TRUE
           do
         ncrit: 
             skip;
         try:
             network := broadcast(network, self, 
                                  [kind |-> "request", clk |-> clock[self]]);
             acks[self] := {};
         enter:
             await /\ Len(reqQ[self]) > 0
                   /\ Head(reqQ[self]).site = self 
                   /\ acks[self] = Sites;
         crit:
             skip;
         exit:
             network := broadcast(network, self, [kind |-> "free"]);
           end while;
       end process;

       process Comm \in Comms
       begin
         comm:
           while TRUE 
           do
             (* pick some sender "from" and the oldest message sent from that node *)
             with me = site(self), 
                  from \in {s \in Sites : Len(network[s][me]) > 0}, 
                  msg = Head(network[from][me]),
                  _net = [network EXCEPT ![from][me] = Tail(@)]
             do
               if msg.kind = "request" then
                  insertRequest(me, from, msg.clk);
                  clock[me] := max(clock[me], msg.clk) + 1;
                  network := send(_net, me, from, [kind |-> "ack"]);
               elsif (msg.kind = "ack") then
                  acks[me] := @ \union {from};
                  network := _net;
               elsif (msg.kind = "free") then
                  removeRequest(me, from);
                  network := _net;
               end if;
             end with;
           end while;
       end process;
     end algorithm
*)

\* BEGIN TRANSLATION
VARIABLES network, clock, reqQ, acks, pc

(* define statement *)
beats(rq1, rq2) ==
  \/ rq1.clk < rq2.clk
  \/ rq1.clk = rq2.clk /\ rq1.site < rq2.site







send(net, from, to, msg) ==
  [net EXCEPT ![from][to] = Append(@, msg)]



broadcast(net, from, msg) ==
  [net EXCEPT ![from] = [to \in Sites |-> Append(net[from][to], msg)]]


vars == << network, clock, reqQ, acks, pc >>

ProcSet == (Sites) \cup (Comms)

Init == (* Global variables *)
        /\ network = [from \in Sites |-> [to \in Sites |-> << >> ]]
        /\ clock = [s \in Sites |-> 1]
        /\ reqQ = [s \in Sites |-> << >>]
        /\ acks = [s \in Sites |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Sites -> "start"
                                        [] self \in Comms -> "comm"]

start(self) == /\ pc[self] = "start"
               /\ pc' = [pc EXCEPT ![self] = "ncrit"]
               /\ UNCHANGED << network, clock, reqQ, acks >>

ncrit(self) == /\ pc[self] = "ncrit"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "try"]
               /\ UNCHANGED << network, clock, reqQ, acks >>

try(self) == /\ pc[self] = "try"
             /\ network' = broadcast(network, self,
                                     [kind |-> "request", clk |-> clock[self]])
             /\ acks' = [acks EXCEPT ![self] = {}]
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << clock, reqQ >>

enter(self) == /\ pc[self] = "enter"
               /\ /\ Len(reqQ[self]) > 0
                  /\ Head(reqQ[self]).site = self
                  /\ acks[self] = Sites
               /\ pc' = [pc EXCEPT ![self] = "crit"]
               /\ UNCHANGED << network, clock, reqQ, acks >>

crit(self) == /\ pc[self] = "crit"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "exit"]
              /\ UNCHANGED << network, clock, reqQ, acks >>

exit(self) == /\ pc[self] = "exit"
              /\ network' = broadcast(network, self, [kind |-> "free"])
              /\ pc' = [pc EXCEPT ![self] = "start"]
              /\ UNCHANGED << clock, reqQ, acks >>

Site(self) == start(self) \/ ncrit(self) \/ try(self) \/ enter(self)
                 \/ crit(self) \/ exit(self)

comm(self) == /\ pc[self] = "comm"
              /\ LET me == site(self) IN
                   \E from \in {s \in Sites : Len(network[s][me]) > 0}:
                     LET msg == Head(network[from][me]) IN
                       LET _net == [network EXCEPT ![from][me] = Tail(@)] IN
                         IF msg.kind = "request"
                            THEN /\ LET entry == [site |-> from, clk |-> (msg.clk)] IN
                                      LET len == Len(reqQ[me]) IN
                                        LET pos == CHOOSE i \in 1 .. len + 1 :
                                                       /\ \A j \in 1 .. i-1 : beats(reqQ[me][j], entry)
                                                       /\ \/ i = len + 1
                                                          \/ beats(entry, reqQ[me][i]) IN
                                          reqQ' = [reqQ EXCEPT ![me] = SubSeq(reqQ[me], 1, pos-1) \circ << entry >>
                                                                       \circ SubSeq(reqQ[me], pos, len)]
                                 /\ clock' = [clock EXCEPT ![me] = max(clock[me], msg.clk) + 1]
                                 /\ network' = send(_net, me, from, [kind |-> "ack"])
                                 /\ acks' = acks
                            ELSE /\ IF (msg.kind = "ack")
                                       THEN /\ acks' = [acks EXCEPT ![me] = @ \union {from}]
                                            /\ network' = _net
                                            /\ reqQ' = reqQ
                                       ELSE /\ IF (msg.kind = "free")
                                                  THEN /\ LET len == Len(reqQ[me]) IN
                                                            LET pos == CHOOSE i \in 1 .. len : reqQ[me][i].site = from IN
                                                              IF (reqQ[me][pos].site = from)
                                                                 THEN /\ reqQ' = [reqQ EXCEPT ![me] = SubSeq(reqQ[me], 1, pos-1) \circ SubSeq(reqQ[me], pos+1, len)]
                                                                 ELSE /\ TRUE
                                                                      /\ reqQ' = reqQ
                                                       /\ network' = _net
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED << network, 
                                                                       reqQ >>
                                            /\ acks' = acks
                                 /\ clock' = clock
              /\ pc' = [pc EXCEPT ![self] = "comm"]

Comm(self) == comm(self)

Next == (\E self \in Sites: Site(self))
           \/ (\E self \in Comms: Comm(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(* -------------------- definitions for verification -------------------- *)

(* constraint for bounding the state space during model checking *)
ClockConstraint == \A s \in Sites : clock[s] <= maxClock

(* set of possible messages exchanged between sites *)
Message ==
  [kind : {"request"}, clk : Nat] \union { [kind |-> "free"], [kind |-> "ack"] }

(* type invariant *)
TypeInvariant ==
  /\ network \in [Sites -> [Sites -> Seq(Message)]]
  /\ clock \in [Sites -> Nat]
  /\ reqQ \in [Sites -> Seq([site : Sites, clk : Nat])]
  /\ \A s \in Sites : \A i \in 1 .. Len(reqQ[s])-1 : beats(reqQ[s][i], reqQ[s][i+1])
  /\ acks \in [Sites -> SUBSET Sites]

(* mutual exclusion *)
Mutex ==
  \A s,t \in Sites : pc[s] = "crit" /\ pc[t] = "crit" => s = t

(* other invariant properties: more complex to evaluate *)
Invariant ==
  /\ (* each queue holds at most one request per site *)
     \A s \in Sites : \A i \in 1 .. Len(reqQ[s]) : 
        \A j \in i+1 .. Len(reqQ[s]) : reqQ[s][j].site # reqQ[s][i].site
  /\ (* requests stay in queue until "free" message received *)
     \A s,t \in Sites :
        (\E i \in 1 .. Len(network[s][t]) : network[s][t][i].kind = "free")
        => \E j \in 1 .. Len(reqQ[t]) : reqQ[t][j].site = s
  /\ (* site is in critical section only if at the head of every request queue *)
     \A s \in Sites : pc[s] = "crit" => \A t \in Sites : Head(reqQ[t]).site = s
     
(* Fairness assumptions for proving liveness *)
Fairness ==
  /\ \A s \in Sites : WF_vars(enter(s)) /\ WF_vars(crit(s)) /\ WF_vars(exit(s))
  /\ \A c \in Comms : WF_vars(comm(c))

LiveSpec == Spec /\ Fairness

Liveness == \A s \in Sites : pc[s] = "enter" ~> pc[s] = "crit"

============================================================================
