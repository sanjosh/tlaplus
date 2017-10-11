------------------------------- MODULE childcare -------------------------------
EXTENDS Naturals, Sequences, TLC, Reals

CONSTANTS CHILDREN,
          ADULTS

ASSUME /\ CHILDREN > 0
			/\  ADULTS > 0

IsEnvSafe(num_children, num_adults) == (num_children = 0) 
     \/ ((num_adults * 3) >= num_children)
	

(*
--algorithm FairProcess {

  variables num_children = 0,
	          num_adults = 0

  process (a \in 1..ADULTS) {
    p0: 
			either { \* adults can enter anytime 
				num_adults := num_adults + 1;
			} 
			or { \* adults exit if insufficient children
				await (num_children = 0 \/ num_adults * 3 > num_children); 
				await (num_adults > 1); \* deadlock if specify gt zero 
				num_adults := num_adults - 1;
				\* print <<num_adults, num_children>>;
			};
		assert IsEnvSafe(num_children, num_adults);
  }

  process (c \in 1..CHILDREN) {
    p0: 
			either { \* children enter if there are sufficient adults 
				await (num_adults > 0 /\ num_adults * 3 > num_children); 
				num_children := num_children + 1;
				\* print <<num_adults, num_children>>;
			} 
			or { \* children can exit anytime 
				await (num_children > 0);
				num_children := num_children - 1;
			};
		assert IsEnvSafe(num_children, num_adults);
  }
}
*)
\* BEGIN TRANSLATION
\* Label p0 of process a at line 22 col 25 changed to p0_
VARIABLES num_children, num_adults, pc

vars == << num_children, num_adults, pc >>

ProcSet == (1..ADULTS) \cup (1..CHILDREN)

Init == (* Global variables *)
        /\ num_children = 0
        /\ num_adults = 0
        /\ pc = [self \in ProcSet |-> CASE self \in 1..ADULTS -> "p0_"
                                        [] self \in 1..CHILDREN -> "p0"]

p0_(self) == /\ pc[self] = "p0_"
             /\ \/ /\ num_adults' = num_adults + 1
                \/ /\ (num_children = 0 \/ num_adults * 3 > num_children)
                   /\ (num_adults > 1)
                   /\ num_adults' = num_adults - 1
             /\ Assert(IsEnvSafe(num_children, num_adults'), 
                       "Failure of assertion at line 31, column 17.")
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED num_children

a(self) == p0_(self)

p0(self) == /\ pc[self] = "p0"
            /\ \/ /\ (num_adults > 0 /\ num_adults * 3 > num_children)
                  /\ num_children' = num_children + 1
               \/ /\ (num_children > 0)
                  /\ num_children' = num_children - 1
            /\ Assert(IsEnvSafe(num_children', num_adults), 
                      "Failure of assertion at line 45, column 17.")
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED num_adults

c(self) == p0(self)

Next == (\E self \in 1..ADULTS: a(self))
           \/ (\E self \in 1..CHILDREN: c(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Oct 09 12:50:02 IST 2017 by sandeep
\* Created Mon Oct 09 12:32:27 IST 2017 by sandeep
