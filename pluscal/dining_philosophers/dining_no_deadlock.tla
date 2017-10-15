------------------------------- MODULE dining_no_deadlock -------------------------------
EXTENDS Naturals, TLC

\* Pluscal options (-termination)


(*
--algorithm Dining {

  variable forks = [i \in 1..5 |-> FALSE];

  fair process (ph \in 1..5) 
		variables tmp; left; right;
	{

		init: 
				right := self;
				if (self = 1) left := 5; else left := self - 1; 
				\* Introduce asymmetry; one philosopher picks right before left
				if (self = 3) { 
					             tmp := left; 
					fake_label1: left := right; 
					             right := tmp; 
				};

		wait_one: { 
								await(forks[left] = FALSE);
		          	forks[left] := TRUE;
							};

		wait_two: { 
		             await(forks[right] = FALSE);
		             forks[right] := TRUE;
						  };

		done_eating: 
							{ 
								 forks[right] := FALSE; 
								 fake_label2: forks[left] := FALSE;  
							}

  }

} (* end Dining *)
*) 
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES forks, pc, tmp, left, right

vars == << forks, pc, tmp, left, right >>

ProcSet == (1..5)

Init == (* Global variables *)
        /\ forks = [i \in 1..5 |-> FALSE]
        (* Process ph *)
        /\ tmp = [self \in 1..5 |-> defaultInitValue]
        /\ left = [self \in 1..5 |-> defaultInitValue]
        /\ right = [self \in 1..5 |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "init"]

init(self) == /\ pc[self] = "init"
              /\ right' = [right EXCEPT ![self] = self]
              /\ IF self = 1
                    THEN /\ left' = [left EXCEPT ![self] = 5]
                    ELSE /\ left' = [left EXCEPT ![self] = self - 1]
              /\ IF self = 3
                    THEN /\ tmp' = [tmp EXCEPT ![self] = left'[self]]
                         /\ pc' = [pc EXCEPT ![self] = "fake_label1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "wait_one"]
                         /\ tmp' = tmp
              /\ forks' = forks

fake_label1(self) == /\ pc[self] = "fake_label1"
                     /\ left' = [left EXCEPT ![self] = right[self]]
                     /\ right' = [right EXCEPT ![self] = tmp[self]]
                     /\ pc' = [pc EXCEPT ![self] = "wait_one"]
                     /\ UNCHANGED << forks, tmp >>

wait_one(self) == /\ pc[self] = "wait_one"
                  /\ (forks[left[self]] = FALSE)
                  /\ forks' = [forks EXCEPT ![left[self]] = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "wait_two"]
                  /\ UNCHANGED << tmp, left, right >>

wait_two(self) == /\ pc[self] = "wait_two"
                  /\ (forks[right[self]] = FALSE)
                  /\ forks' = [forks EXCEPT ![right[self]] = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "done_eating"]
                  /\ UNCHANGED << tmp, left, right >>

done_eating(self) == /\ pc[self] = "done_eating"
                     /\ forks' = [forks EXCEPT ![right[self]] = FALSE]
                     /\ pc' = [pc EXCEPT ![self] = "fake_label2"]
                     /\ UNCHANGED << tmp, left, right >>

fake_label2(self) == /\ pc[self] = "fake_label2"
                     /\ forks' = [forks EXCEPT ![left[self]] = FALSE]
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << tmp, left, right >>

ph(self) == init(self) \/ fake_label1(self) \/ wait_one(self)
               \/ wait_two(self) \/ done_eating(self) \/ fake_label2(self)

Next == (\E self \in 1..5: ph(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..5 : WF_vars(ph(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
