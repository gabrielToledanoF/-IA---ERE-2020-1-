/*Código por Gabriel Toledano Feitosa para a solução dos exércicios 21.1, 21.2 e 21.3 do livro "Prolog Programming For Artificial Intelligence 4th edition"*/
parent(pam, bob).
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).
parent(pat, jim).
parent(pat, eve).

male(tom).
male(bob).
male(jim).
female(pam).
female(liz).
female(ann).
female(pat).
female(eve).

/*Questão 21.1
%Exemplo has_daughter
backliteral(parent(X,Y),[X,Y]). %background literal with vars [X,Y]
backliteral(male(X),[X]).
backliteral(female(X),[X]).

prolog_predicate(parent(_,_)). %goal executed directly by Prolog
prolog_predicate(male(_)).
prolog_predicate(female(_)).

%Positive Examples

ex(has_daughter(tom)).
ex(has_daughter(bob)).
ex(has_daughter(pat)).

%Negative Examples

nex(has_daughter(pam)).
nex(has_daughter(jim)).

%Starting Hypothesis
start_hyp([[has_daughter(X)] / [X]]).
*/

/*
%Questao 21.2
backliteral([parent(X,Y)],[X,Y]).
backliteral([predecessor(X,Y)],[X,Y]).
prolog_predicate(parent(X,Y)).
*/


%Questão 21.3
backliteral([atom(X), parent(X,Y)],[X,Y]).
backliteral([atom(X), predecessor(X,Y)],[X,Y]).

prolog_predicate(parent(X,Y)).
prolog_predicate(atom(X)).


ex(predecessor(pam, bob)).
ex(predecessor(pam, jim)).
ex(predecessor(tom, ann)).
ex(predecessor(tom, jim)).
ex(predecessor(tom, liz)).

nex(predecessor(liz, bob)).
nex(predecessor(pat, bob)).
nex(predecessor(pam, liz)).
nex(predecessor(liz, jim)).
nex(predecessor(liz, liz)).

start_hyp([[predecessor(X1, Y1)]/[X1, Y1],
	[predecessor(X2, Y2)]/[X2, Y2]]).



%Loop-avoiding Interpreter
%prove (Goal, Hypo, Answer).
%Answer yes if derivable from Hypo in at most D steps
% no if not derivable
% maybe if search terminated after D steps inconclusively

prove(Goal, Hypo, Answer) :-
	max_proof_length(D),
	prove(Goal, Hypo, D, RestD),
		(RestD >= 0, Answer = yes;
		 RestD < 0, !, Answer = maybe
		 ).
prove(_,_,no). %Otherwise, Goal Definitely cannot be proved

prove(_, _, D, D):-
	D < 0, !. %Proof length overstepped

prove([],_,D,D) :- !.

prove([G1|Gs], Hypo, D0, D):- !,
	prove(G1,Hypo, D0, D1),
	prove(Gs,Hypo, D1, D).

prove(G,_,D,D):-
	prolog_predicate(G),
	call(G).

prove(G, Hyp, D0, D) :-
	D0 =< 0, !, D is D0 - 1
	;
	D1 is D0 - 1,
	member(Clause/_, Hyp),
	copy_term(Clause,[Head|Body]),
	G = Head,
	prove(Body, Hyp, D1, D).


%Mini-Hyper

%Implementação de um contador global retirado de: https://stackoverflow.com/questions/10655013/how-to-create-global-variable-in-prolog/13956397
add_hyp :- nb_getval(counter_hypothesis, C), Cnew is C+1, nb_setval(counter_hypothesis, Cnew).
add_refine :- nb_getval(counter_refinements, C), Cnew is C+1, nb_setval(counter_refinements, Cnew).

induce(Hyp) :-
	statistics(walltime, [TimeSinceStart | [TimeSinceLastCall]]),
	b_setval(counter_hypothesis, 0),
	b_setval(counter_refinements, 0),
	iter_deep(Hyp, 0), %start with max depth 0
	statistics(walltime, [NewTimeSinceStart | [ExecutionTime]]),
    write('Execution took '), write(ExecutionTime), write(' ms.'), nl.

iter_deep(Hyp,MaxD):-
    write('MaxD= '), write(MaxD), nl,
    start_hyp(Hyp0),
    complete(Hyp0),
    depth_first(Hyp0,Hyp,MaxD),
    nb_getval(counter_hypothesis, Ch),
    nb_getval(counter_refinements, Cr),
	print('Hyp = '),print(Ch),nl,
	print('Ref = '),print(Cr),nl
    ;
    NewMaxD is MaxD+1,
    iter_deep(Hyp, NewMaxD).


%Refine Hyp0 into consistent and complete Hyp in at most MaxD steps


depth_first(Hyp, Hyp, _):-
	consistent(Hyp).

depth_first(Hyp0, Hyp, MaxD0):-
	MaxD0 > 0,
	MaxD1 is MaxD0 - 1,
	add_refine,
	refine_hyp(Hyp0, Hyp1),
	complete(Hyp1), %Hyp1 covers all positive examples
	depth_first(Hyp1, Hyp, MaxD1).

complete(Hyp):- %hyp covers all positive examples
	not(ex(E),
		once(prove(E, Hyp, Answer)),
		Answer \== yes). 

consistent(Hyp):- %Hyp does not possibly cover any negative example
	not(nex(E),
		once(prove(E,Hyp, Answer)),
		Answer \== no).

%refine(Clause, Args, NewClause, NewArgs)
%refine Clause with arguments Args giving NewClause with NewArgs

refine_hyp(Hyp0, Hyp):- %Refine Hyp0 into Hyp
	%Choose Clause0 from Hyp0
	conc(Clauses1, [Clause0/Vars0 | Clauses2], Hyp0),
	%New hypotheshis 
	%AKI add_hyp
	add_hyp,
	conc(Clauses1, [Clause/Vars | Clauses2], Hyp),
	%Refine the Clause
	refine(Clause0, Vars0, Clause, Vars).



%Refine by unifying arguments

refine(Clause, Args, Clause, NewArgs):-
	conc(Args1,[A | Args2], Args),
	member(A, Args2),
	conc(Args1, Args2, NewArgs).

%Refine by adding a literal

refine(Clause, Args, NewClause, NewArgs):-
	length(Clause, L),
	max_clause_length(MaxL),
	L < MaxL,
	backliteral(Lit, Vars),
	conc(Clause, [Lit], NewClause),
	conc(Args, Vars, NewArgs).


%MiniHyper Default Parameter Settings

max_proof_length(6).

max_clause_length(3).
          
%Aux
conc([],L,L).
conc([X|T],L,[X|L1]):-
    conc(T,L,L1).

not(A,B,C):-
    A,
    B,
    C, !, fail.
not(_,_,_).
