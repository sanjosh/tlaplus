------------------------------- MODULE childcare2 -------------------------------
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
    	 a0: num_adults := num_adults + 1;
			 a1 : { 
				await ((num_adults - 1) * 3 >= num_children);
				num_adults := num_adults - 1;
			 	assert IsEnvSafe(num_children, num_adults);
				 };
			goto a0;
  }

  process (c \in 1..CHILDREN) {
    	p0: { \* children enter if there are sufficient adults 
				await (num_adults * 3 >= num_children + 1);
				num_children := num_children + 1;
				assert IsEnvSafe(num_children, num_adults);
				};
			p1 : num_children := num_children - 1;
		  goto p0;
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES num_children, num_adults, pc

vars == << num_children, num_adults, pc >>

ProcSet == (1..ADULTS) \cup (1..CHILDREN)

Init == (* Global variables *)
        /\ num_children = 0
        /\ num_adults = 0
        /\ pc = [self \in ProcSet |-> CASE self \in 1..ADULTS -> "a0"
                                        [] self \in 1..CHILDREN -> "p0"]

a0(self) == /\ pc[self] = "a0"
            /\ num_adults' = num_adults + 1
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED num_children

a1(self) == /\ pc[self] = "a1"
            /\ (num_children = 0 \/ ((num_adults - 1) * 3 >= num_children))
            /\ num_adults' = num_adults - 1
            /\ Assert(IsEnvSafe(num_children, num_adults'), 
                      "Failure of assertion at line 25, column 33.")
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ UNCHANGED num_children

a(self) == a0(self) \/ a1(self)

p0(self) == /\ pc[self] = "p0"
            /\ (num_adults * 3 >= num_children + 1)
            /\ num_children' = num_children + 1
            /\ Assert(IsEnvSafe(num_children', num_adults), 
                      "Failure of assertion at line 34, column 33.")
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED num_adults

p1(self) == /\ pc[self] = "p1"
            /\ num_children' = num_children - 1
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED num_adults

c(self) == p0(self) \/ p1(self)

Next == (\E self \in 1..ADULTS: a(self))
           \/ (\E self \in 1..CHILDREN: c(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
