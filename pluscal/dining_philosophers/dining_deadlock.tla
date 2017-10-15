------------------------------- MODULE dining_deadlock -------------------------------
EXTENDS Naturals, TLC

\* this solution will Deadlock

(*
--algorithm DiningPhilosophers {

  variable forks = [i \in 1..5 |-> FALSE];

  process (ph \in 1..5) 
		variables left; right;
	{

		init: {
				     right := self;
				     if (self = 1) left := 5; else left := self - 1; 
			    };

		wait_first_fork: 
		          { 
								await(forks[left] = FALSE);
		          	forks[left] := TRUE;
							};

		wait_second_fork: 
		          { 
		             await(forks[right] = FALSE);
		             forks[right] := TRUE;
						  };

		done_eating: 
							{ 
								 forks[right] := FALSE; 
								 \* fake label fl2 otherwise won't compile
								 fl2: forks[left] := FALSE;  
							}

  }

} (* end Dining *)
*) 
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES forks, pc, left, right

vars == << forks, pc, left, right >>

ProcSet == (1..5)

Init == (* Global variables *)
        /\ forks = [i \in 1..5 |-> FALSE]
        (* Process ph *)
        /\ left = [self \in 1..5 |-> defaultInitValue]
        /\ right = [self \in 1..5 |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "init"]

init(self) == /\ pc[self] = "init"
              /\ right' = [right EXCEPT ![self] = self]
              /\ IF self = 1
                    THEN /\ left' = [left EXCEPT ![self] = 5]
                    ELSE /\ left' = [left EXCEPT ![self] = self - 1]
              /\ pc' = [pc EXCEPT ![self] = "wait_first_fork"]
              /\ forks' = forks

wait_first_fork(self) == /\ pc[self] = "wait_first_fork"
                         /\ (forks[left[self]] = FALSE)
                         /\ forks' = [forks EXCEPT ![left[self]] = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = "wait_second_fork"]
                         /\ UNCHANGED << left, right >>

wait_second_fork(self) == /\ pc[self] = "wait_second_fork"
                          /\ (forks[right[self]] = FALSE)
                          /\ forks' = [forks EXCEPT ![right[self]] = TRUE]
                          /\ pc' = [pc EXCEPT ![self] = "done_eating"]
                          /\ UNCHANGED << left, right >>

done_eating(self) == /\ pc[self] = "done_eating"
                     /\ forks' = [forks EXCEPT ![right[self]] = FALSE]
                     /\ pc' = [pc EXCEPT ![self] = "fl2"]
                     /\ UNCHANGED << left, right >>

fl2(self) == /\ pc[self] = "fl2"
             /\ forks' = [forks EXCEPT ![left[self]] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << left, right >>

ph(self) == init(self) \/ wait_first_fork(self) \/ wait_second_fork(self)
               \/ done_eating(self) \/ fl2(self)

Next == (\E self \in 1..5: ph(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
