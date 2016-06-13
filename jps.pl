variables([a, b, c, d, e]).

known_fact(rodzic(a,b)).
known_fact(siostra(c,a)).
known_fact(brat(d,a)).
known_fact(ciocia(c,b)).
known_fact(wujek(d,b)).

predicate(rodzic,2).
predicate(siostra,2).
predicate(ciocia,2).
predicate(wujek,2).

item(ItemNo, [LF|LR], Ret):-
	ItemNo>0,
	ItemNoNew is ItemNo - 1,
	item(ItemNoNew, LR, Ret).

item(0, [LF|_], LF).

insert_arg(LastUsed, LastLocal, _, Z, LastLocal, yes):-
	between(0, LastUsed, X),
	variables(Variables),
	item(X, Variables, Z).

insert_arg(LastUsed, LastLocal,  Flag, Z, LastLocal, Flag):-
	FirstLocalUsed is LastUsed + 1,
	between(FirstLocalUsed, LastLocal, X),
	variables(Variables),
	item(X, Variables, Z).

insert_arg(_, LastLocal, Flag, Z, RetLastLocal, Flag):-
	RetLastLocal is LastLocal+1,
	variables(Variables),
	item(RetLastLocal, Variables, Z).


build_arg_list(N, vars(LastUsed, LastLocal), Flag, [NewArg|ArgList], RetLastUsed) :-
	N>1,
	insert_arg(LastUsed, LastLocal, Flag, NewArg, NewLastLocal, NewFlag),
	N2 is N-1,
	build_arg_list(N2, vars(LastUsed, NewLastLocal), NewFlag, ArgList, RetLastUsed).


build_arg_list(1, vars(LastUsed, LastLocal), yes, [LastArg], NewLastLocal) :-
	insert_arg(LastUsed, LastLocal, yes, LastArg, NewLastLocal, _).

build_arg_list(1, vars(LastUsed, LastLocal), no, [LastArg], LastLocal) :-
	between(0, LastUsed, X),
	variables(Variables),
	item(X, Variables, LastArg).

% Sprawdza dopasowanie listy argumentów wyrażenia predykatowego z poprzednika i listy argumentów faktu
% operacyjnego w kontekście dotychczasowych związań zmiennych. W przypadku powodzenia jako wynik
% zwraca uzupełnioną listę związań zmiennych.
match_arg_lists([ ] ,[ ], Bindings, Bindings) .

match_arg_lists([Arg1|Rest1], [Arg2|Rest2], BindingsIn, BindingsOut) :-
	match_args(Arg1, Arg2, BindingsIn, Bindings1),
	match_arg_lists(Rest1, Rest2, Bindings1, BindingsOut) .

% Sprawdza dopasowanie pary argumentów--zmiennej z wyrażenia predykatowego z poprzednika reguły i
% symbolu z faktu operacyjnego. W przypadku powodzenia jako wynik zwraca uzupełnioną listę związań
% zmiennych.

match_args(Arg1, Arg2, [], [binding(Arg1, Arg2)]):-!.

match_args(Arg1, Arg2, [binding(Arg1, Arg2)|Rest], [binding(Arg1, Arg2)|Rest]):-!.

match_args(Arg1, Arg2, [binding(A,V)|Rest], [binding(A,V)|Ret]):-
	Arg1 \= A,
	Arg2 \= V,
	match_args(Arg1, Arg2, Rest, Ret).

%match_args(X,Y,[],[binding(X,Y)]):-!.
%match_args(X,Y,[binding(X,Y)|Bindings],[binding(X,Y)|Bindings]):-!.
%match_args(Arg1,Arg2,[binding(X,Y)|Bindings],[binding(X,Y)|NewBindings]):- Arg1\=X,Arg2\=Y,match_args(Arg1,Arg2,Bindings,NewBindings).


%Poszukuje pokrycia w faktach operacyjnych dla pojedynczego prostego wyrażenia predykatowego z
%poprzednika.
match_expr(Expr,BindingsIn,BindingsOut) :-
	known_fact(Fact),
	functor(Expr,Functor,N),
	functor(Fact,Functor,N),
	Expr =.. [_|ArgList1],
	Fact =.. [_|ArgList2],
	match_arg_lists(ArgList1,ArgList2,BindingsIn,BindingsOut) .

%Poszukuje pokrycia dla poprzednika w faktach operacyjnych.
%Procedura rekurencyjna: na każdym poziomie rekurencji szuka w faktach operacyjnych pokrycia dla kolejnego
%członu koniunktywnego poprzednika, w kontekście dotychczas otrzymanych związań zmiennych.
match_anteced([ ], Bindings, Bindings) .

match_anteced([A|RestAnteced], BindingsIn, BindingsOut) :-
	match_expr(A, BindingsIn, Bindings1),
	match_anteced(RestAnteced, Bindings1, BindingsOut) .

%Porównuje następnik z przykładem, w przypadku powodzenia jako wynik zwraca związania zmiennych
match_conseq(Conseq, Example, BindingsOut) :-
	Conseq =.. [_|ArgList1],
	Example =.. [_|ArgList2],
	match_arg_lists(ArgList1,ArgList2,[],BindingsOut).


%Sprawdzanie pokrycia przykładu przez regułę:
%1. uzgodnienie następnika z przykładem: wynikiem jest lista związań zmiennych
%2. dla każdego członu koniunktywnego poprzednika:
 %--poszukiwanie faktu operacyjnego uzgadnialnego z tym członem poprzednika
 %w kontekście dotychczasowych związań zmiennych
%--w przypadku powodzenia nowe związania zmiennych zostają dołączone do listy.
covers(rule(Conseq, Anteced), Example) :-
	match_conseq(Conseq, Example, Bindings),
	match_anteced(Anteced, Bindings, _ ) .

%Procedura usuwa z zadanego zbioru przykładów przykłady pokryte przez podaną regułę.
remove([],_,[]).

remove([FirstEx|RestEx],Rule,RestPosExamples):-
	covers(Rule,FirstEx),!,
	remove(RestEx,Rule,RestPosExamples).

remove([FirstEx|RestEx],Rule,[FirstEx|Rest]):-
	remove(RestEx,Rule,Rest).


/******************************************************************************************************************************************
* choose_best(Rules,BestRule,RetLastUsed) 
******************************************************************************************************************************************/

choose_best(Rules,BestRule,RetLastUsed):-maxscore_rule(Rules,rule_descr(BestRule,_,RetLastUsed)).

maxscore_rule([Rule], Rule).

maxscore_rule([rule_descr(Rule1,Score1,LastUsed1)|Rest], rule_descr(Rule1,Score1,LastUsed1)):-
	maxscore_rule(Rest, rule_descr(Rule2,Score2,LastUsed2)),
	Score1>Score2.

maxscore_rule([rule_descr(Rule1,Score1,LastUsed1)|Rest], rule_descr(Rule2,Score2,LastUsed2)):-
	maxscore_rule(Rest, rule_descr(Rule2,Score2,LastUsed2)),
	Score1=<Score2.

member1(X,[X|_]).
member1(X,[Y|Rest]) :-
    member1(X, Rest).

filter( Examples, Rule, FilteredExamples) :-
    findall( Example, (member1(Example, Examples), covers(Rule, Example)), FilteredExamples).
	

%Procedura sprawdza jeden z warunków wstępnych przydatności zbudowanej reguły cząstkowej: czy reguła
%eliminuje przynajmniej jeden przykład negatywny.
suitable(rule(Conseq,Anteced),NegExamples):- 
	member1(Example,NegExamples), 
	not(covers(rule(Conseq,Anteced),NegExample)).


build_expr(LastUsed,Expr,RetLastUsed) :-
	predicate(Pred, N),
	build_arg_list(N, vars(LastUsed, LastUsed), false, ArgList, RetLastUsed),
	Expr =.. [Pred|ArgList] .

candidate_rule(rule(Conseq, Anteced), PosExamples, NegExamples, LastUsed, rule(Conseq, [Expr|Anteced]), RetLastUsed) :-
	build_expr(LastUsed, Expr, RetLastUsed),
	suitable(rule(Conseq, [Expr|Anteced]), NegExamples) .
	

scored_rule( PosExamples, NegExamples, PartialRule, LastUsed, rule_descr(CandPartialRule, Score, RetLastUsed) ) :-
	candidate_rule(PartialRule, PosExamples, NegExamples, LastUsed, CandPartialRule, RetLastUsed),
	filter( PosExamples, CandPartialRule, PosExamples1),
	filter( NegExamples, CandPartialRule, NegExamples1),
	length( PosExamples1, NPos),
	length(NegExamples1, NNeg),
	NPos > 0,
	Score is NPos - NNeg.
	
%Wykonuje krok budowania koniunktywnego poprzednika reguły, tworząc nową regułę cząstkową. Spośród
%wszystkich możliwych nowych reguł cząstkowych, powstałych przez dodanie do dotychczas zbudowanej
%koniunkcji nowego wyrażenia predykatowego, jest wybierana reguła o najwyższej ocenie heurystycznej.
%Procedura new_partial_rule wywołuje procedurę wbudowaną findall, która wywołując i wymuszając
%nawroty do procedury scored_rule zbiera wszystkie możliwe nowe reguły cząstkowe, powstałe przez dodanie
%do dotychczas zbudowanej koniunkcji nowego wyrażenia predykatowego, wraz z ocenami.
%Następnie procedura new_partial_rule korzysta z procedury
%choose_best – w celu wybrania z otrzymanego zbioru reguł cząstkowych tej o najwyższej ocenie
%heurystycznej
new_partial_rule( PosExamples, NegExamples, PartialRule, LastUsed, BestRule, RetLastUsed) :-
	findall(NewRuleDescr, scored_rule( PosExamples, NegExamples, PartialRule, LastUsed, NewRuleDescr), Rules),
	choose_best( Rules, BestRule, RetLastUsed).

%Procedura buduje jedną regułę do zbioru reguł wzorca. W każdym kroku rekurencyjnym procedura wywołuje
%procedurę new_partial_rule w celu dodania nowego wyrażenia predykatowego do poprzednika budowanej
%reguły, a następnie filtruje przykłady, wybierając te pokryte przez zbudowaną nową regułę cząstkową.

learn_one_rule( _ , [ ] , Rule, _ , Rule).

learn_one_rule( PosExamples, NegExamples, PartialRule, LastUsed, Rule ) :-
	new_partial_rule( PosExamples, NegExamples, PartialRule, LastUsed, NewPartialRule, NewLastUsed) ,
	filter( PosExamples, NewPartialRule, PosExamples1),
	filter( NegExamples, NewPartialRule, NegExamples1),
	learn_one_rule( PosExamples1, NegExamples1, NewPartialRule, NewLastUsed, Rule ) .

%Procedura buduje zbiór reguł wzorca. W każdym kroku rekurencyjnym procedura wywołuje procedurę
%learn_one_rule, w celu zbudowania jednej reguły.
%Procedura learn_rules korzysta z procedur:
%learn_one_rule -- w celu zbudowania jednej reguły.
%remove - w celu usunięcia ze zbioru przykładów tych pokrytych przez zbudowaną regułę

learn_rules( [ ] , _ , _ , _ , [ ] ) .

learn_rules(PosExamples, NegExamples, Conseq, VarsIndex, [Rule | RestRules]) :-
	learn_one_rule( PosExamples, NegExamples, rule(Conseq, [ ]), VarsIndex, Rule ) ,
	remove( PosExamples, Rule, RestPosExamples),
	learn_rules(RestPosExamples, NegExamples, Conseq, VarsIndex, RestRules) .

gen_arg_list(N, Result) :-
	variables(Variables),
	gen_args(Variables, N, Result).

gen_args(ArgList, 0, []).

gen_args(ArgList, N, [Arg|Rest]):-
	member(Arg, ArgList),
	N>0,
	N2 is N - 1,
        gen_args(ArgList, N2, Rest).



check_args_not_fitting([Arg|Rest1],[Arg|Rest2]) :- check_args_not_fitting(Rest1,Rest2).
check_args_not_fitting([Arg1|Rest1],[Arg2|Rest2]) :- Arg1 \= Arg2.


not_fitting([Positive|Rest], Args):-
	Positive =.. [_|PosArgs],
	check_args_not_fitting(PosArgs,Args),
	not_fitting(Rest, Args).
not_fitting([], Args).


gen_negative_examples(Positive, Conseq, NotFittingList):-
	findall(NegExample, (functor(Conseq, Functor, N), gen_arg_list(N, GenArgs), not_fitting(Positive, GenArgs), NegExample =..[Functor| GenArgs] ),NotFittingList).

learn(Conseq, Rules) :-
	functor(Conseq, Functor,N),
	findall(A, (known_fact(A) ,functor(A,Functor,N)),Positive),
	gen_negative_examples(Positive, Conseq, Negative),
	learn_rules(Positive, Negative, Conseq, 0, Rules).
	
	
