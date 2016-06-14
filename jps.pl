variables([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z]).

% build_arg_list
% Konstruuje liste argumentow - w postaci kombinacji zmiennych -  dla wyrazenia predykatowego

build_arg_list(N, vars(LastUsed, LastLocal), Flag, [NewArg|ArgList], RetLastUsed) :-
	N>1,
	insert_arg(LastUsed, LastLocal, Flag, NewArg, NewLastLocal, NewFlag),
	N2 is N-1,
	build_arg_list(N2, vars(LastUsed, NewLastLocal), NewFlag, ArgList, RetLastUsed).

% nie dodano jeszcze zmiennej globalnej
build_arg_list(1, vars(LastUsed, LastLocal), false, [LastArg], NewLastLocal) :-
	insert_arg(LastUsed, LastLocal, false, LastArg, NewLastLocal, true).

% dodano już zmienną globalna
build_arg_list(1, vars(LastUsed, LastLocal), true, [LastArg], LastLocal) :-
	insert_arg(LastUsed, LastLocal, true, LastArg, LastLocal, _).


% insert_arg
% Generuje argument dla obsadzanej pozycji

%! Dodawanie nowej zmiennej
insert_arg(_, LastLocal, Flag, Z, RetLastLocal, Flag):-
	RetLastLocal is LastLocal+1,
	variables(Variable),
	itemAtPos(RetLastLocal, Variable, Z).

%! Dodawanie zmiennej juz uzytej lokalnie, ale nie uzytej globalnie
insert_arg(LastUsed, LastLocal,  Flag, Z, LastLocal, Flag):-
	FirstLocalUsed is LastUsed + 1,
	between(FirstLocalUsed, LastLocal, X),
	variables(Variable),
	itemAtPos(X, Variable, Z).

%! Dodawanie zmiennej uzytej globalnie
insert_arg(LastUsed, LastLocal, _, Z, LastLocal, true):-
	between(1, LastUsed, X),
	variables(Variables),
	itemAtPos(X, Variables, Z).


% zwraca element na zadanej pozycji
itemAtPos(1, [LF|_], LF).

itemAtPos(ItemNo, [_|LR], Ret):-
	itemAtPos(ItemNoNew, LR, Ret),
	ItemNo is ItemNoNew + 1.


% proceduda covers
covers(rule(Conseq,Anteced),Example):-
	match_conseq(Conseq,Example,Bindings),
	match_anteced(Anteced,Bindings,_).


% procedura match conseq
match_conseq(Conseq,Example,BindingsOut):-
	Conseq=..[_|ArgList1],
	Example=..[_|ArgList2],
	match_arg_lists(ArgList1,ArgList2,[],BindingsOut).


% procedura match anteced
match_anteced([],Bindings,Bindings).

match_anteced([A|RestAntenced],BindingsIn,BindingsOut):-
	match_expr(A,BindingsIn,Bindings1),
	match_anteced(RestAntenced,Bindings1,BindingsOut).


% procedura match expr
match_expr(Expr,BindingsIn,BindingsOut):-
	known_fact(Fact),
	functor(Expr,Functor,N),
	functor(Fact,Functor,N),
	Expr=..[_|ArgList1],
	Fact=..[_|ArgList2],
	match_arg_lists(ArgList1,ArgList2,BindingsIn,BindingsOut).


% procedura match arg lists
match_arg_lists([],[],Bindings,Bindings).

match_arg_lists([Arg1|Rest1],[Arg2|Rest2],BindingsIn,BindingsOut):-
	match_args(Arg1,Arg2,BindingsIn,Bindings1),
	match_arg_lists(Rest1,Rest2,Bindings1,BindingsOut).


% procedura match args
match_args(Arg1, Arg2, [], [binding(Arg1, Arg2)]):-!.

match_args(Arg1, Arg2, [binding(Arg1, Arg2)|Rest], [binding(Arg1, Arg2)|Rest]):-!.

match_args(Arg1, Arg2, [binding(A,V)|Rest], [binding(A,V)|Ret]):-
	Arg1 \= A,
	Arg2 \= V,
	match_args(Arg1, Arg2, Rest, Ret).


% proceduda member1
member1(X,[X|_]).
member1(X,[_|Rest]) :-
	member1(X, Rest).


% proceduda filter
filter(Examples,Rule,Examples1):-
	findall(Example,(member1(Example,Examples),covers(Rule,Example)),Examples1).


% procedura build expr
build_expr(LastUsed,Expr,RetLastUsed):-
	predicate(Pred,N),
	build_arg_list(N,vars(LastUsed,LastUsed),false,ArgList,RetLastUsed),
	Expr=..[Pred|ArgList].


append_element(X,[],[X]).
append_element(X,[First|Rest],[First|NewRest]):-
	append_element(X,Rest,NewRest).


% procedura candidate rule
candidate_rule(rule(Conseq,Anteced),_,NegExamples,LastUsed,rule(Conseq,[Expr|Anteced]),RetLastUsed):-
	build_expr(LastUsed,Expr,RetLastUsed),
	suitable(rule(Conseq,[Expr|Anteced]),NegExamples).


% procedura scored rule
scored_rule(PosExamples,NegExamples,PartialRule,LastUsed,rule_descr(CandPartialRule,Score,RetLastUsed)):-
	candidate_rule(PartialRule,PosExamples,NegExamples,LastUsed,CandPartialRule,RetLastUsed),
	filter(PosExamples,CandPartialRule,PosExamples1),
	filter(NegExamples,CandPartialRule,NegExamples1),
	length(PosExamples1,NPos),
	length(NegExamples1,NNeg),
	NPos>0,
	Score is NPos - NNeg.


% procedura new partial rule
new_partial_rule( PosExamples, NegExamples, PartialRule, LastUsed, BestRule, RetLastUsed) :-
	findall(NewRuleDescr, scored_rule( PosExamples, NegExamples, PartialRule, LastUsed, NewRuleDescr), Rules),
	choose_best( Rules, BestRule, RetLastUsed).

% procedura learn one rule
learn_one_rule( _ , [ ] , Rule, _ , Rule).

learn_one_rule( PosExamples, NegExamples, PartialRule, LastUsed, Rule ) :-
	new_partial_rule( PosExamples, NegExamples, PartialRule, LastUsed, NewPartialRule, NewLastUsed),
	filter( PosExamples, NewPartialRule, PosExamples1),
	filter( NegExamples, NewPartialRule, NegExamples1),
	learn_one_rule( PosExamples1, NegExamples1, NewPartialRule, NewLastUsed, Rule ).

% procedura learn rules
learn_rules( [ ] , _ , _ , _ , [ ] ).

learn_rules(PosExamples, NegExamples, Conseq, VarsIndex, [Rule | RestRules]) :-
	learn_one_rule( PosExamples, NegExamples, rule(Conseq, [ ]), VarsIndex, Rule ),
	remove( PosExamples, Rule, RestPosExamples),
	learn_rules(RestPosExamples, NegExamples, Conseq, VarsIndex, RestRules).


% procedura suitable
suitable(rule(Conseq,Anteced),NegExamples):- 
	member1(Example,NegExamples), 
	not(covers(rule(Conseq,Anteced),NegExamples)),
	!.


% procedura choose best
choose_best(Rules,BestRule,RetLastUsed):-
	maxscore_rule(Rules,rule_descr(BestRule,_,RetLastUsed)).

% procedura max score rule
maxscore_rule([Rule], Rule).

maxscore_rule([rule_descr(Rule1,Score1,LastUsed1)|Rest],rule_descr(MRule,MScore,MLastUsed)):-
	maxscore_rule(Rest, rule_descr(_,Score2,_)),
	Score1 > Score2,
	MRule = Rule1,
	MScore = Score1,
	MLastUsed = LastUsed1.

maxscore_rule([rule_descr(_,Score1,_)|Rest],rule_descr(MRule,MScore,MLastUsed)):-
	maxscore_rule(Rest,rule_descr(Rule2,Score2,LastUsed2)),
	Score1 =< Score2,
	MRule = Rule2,
	MScore = Score2,
	MLastUsed = LastUsed2.


% procedura remove
remove([],_,[]).

remove([FirstEx|RestEx],Rule,RestPosExamples):-
	covers(Rule,FirstEx),!,
	remove(RestEx,Rule,RestPosExamples).

remove([FirstEx|RestEx],Rule,[FirstEx|Rest]):-
	remove(RestEx,Rule,Rest).

/******************************************************************************************************************************************
* learn()
* zrobic : - liste predykatow do uczenia sie , np predicate(matka, 2).  2- liczba argumentow
*          - Liste list przykladowa pozytywnych/negatywnych
*           -
******************************************************************************************************************************************/

learn(Predicate,Rules):-
  Predicate =..[PredName|PredArgs],length(PredArgs,N),
  get_idx(PredArgs,Idxs),
  max_idx(Idxs,LastUsed),
  findall(PosEx, find_pos(PredName,N,PosEx),PosExamples),
  findall(NegEx,find_neg(PredName,N,NegEx),NegExamples),
  learn_rules(PosExamples,NegExamples,Predicate,LastUsed,Rules).
  
get_idx([],[]).
get_idx([Arg|RestArg],[Idx|RestIdx]):-variables(L),itemAtPos(Idx,L,Arg),get_idx(RestArg,RestIdx).

max_idx([Idx], Idx).
max_idx([Idx1|Rest],Max):-max_idx(Rest,Idx2),Idx1>Idx2,Max=Idx1.
max_idx([Idx1|Rest],Max):-max_idx(Rest,Idx2),Idx1=<Idx2,Max=Idx2.


find_pos(PredName,ArgLen,Expr):-
  known_fact(Expr),Expr=..[PredName|Args],length(Args,N), N is ArgLen.

find_neg(PredName,ArgLen,Expr):-
  object_list(ObjList),make_perm(ObjList,ArgLen,Args),
  Expr=..[PredName|Args],not(known_fact(Expr)).

object_list(ObjList):-
  findall(Expr,known_fact(Expr),ExprList),object_list_rec([],ExprList,ObjList).
object_list_rec(Res,[],Res).
object_list_rec(ObjList,[Expr|Rexpr],Result):-
  Expr=..[_|Objs],add_to_list(ObjList,Objs,ParRes),object_list_rec(ParRes,Rexpr,Result).

add_to_list(List,[X|RestToAdd],[X|FilteredList]):-
  not(member1(X,List)),not(member1(X,RestToAdd)),add_to_list(List,RestToAdd,FilteredList).
add_to_list(List,[X|RestToAdd],FilteredList):-
  member1(X,RestToAdd),add_to_list(List,RestToAdd,FilteredList).
add_to_list(List,[X|RestToAdd],FilteredList):-
  member1(X,List),add_to_list(List,RestToAdd,FilteredList).
add_to_list(List,[],List).

make_perm(_,0,[]).
make_perm(ObjList,N,[X|Rest]):-
  N>0,member1(X,ObjList),delete(ObjList,X,NewObjList),N1 is N-1,make_perm(NewObjList,N1,Rest).


known_fact(syn(tomek,adam)).
known_fact(syn(adam,wojtek)).
known_fact(wnuk(tomek,wojtek)).


known_fact(syn(marcin,piotr)).
known_fact(syn(piotr,jerzy)).
known_fact(wnuk(marcin,jerzy)).

known_fact(syn(krzysztof,wiktor)).
known_fact(syn(wiktor,bohdan)).
known_fact(wnuk(krzysztof,bohdan)).

known_fact(syn(tomeka,adama)).
known_fact(syn(adama,wojteka)).
known_fact(wnuk(tomeka,wojteka)).

known_fact(syn(marcina,piotra)).
known_fact(syn(piotra,jerzya)).
known_fact(wnuk(marcina,jerzya)).

known_fact(syn(janusz,anna)).
known_fact(corka(anna,mariusz)).
known_fact(wnuk(janusz,mariusz)).

known_fact(syn(adrian,magda)).
known_fact(corka(magda,michal)).
known_fact(wnuk(adrian,michal)).


predicate(syn,2).
predicate(corka,2).
