%!! Penser à charger ABox et Tbox

%Démarrage du programme
programme :-
	premiere_etape(Tbox,Abi,Abr),
	deuxieme_etape(Abi,Abi1,Tbox),
	troisieme_etape(Abi1,Abr).

%Partie 1 - abi : ABox assertions de concept, abi1 : Abox assertions de roles


tbox(Tbox) :- findall((C,CG),(equiv(C,CG)),Tbox).
abi(Abi) :- findall((I,C),(inst(I,C)),Abi).
abr(Abr) :- findall((I,I2,R),(instR(I,I2,R)),Abr).

premiere_etape(Tbox,Abi,Abr):- tbox(Tbox),!,abi(Abi),!,abr(Abr),!.
	
% Partie 2
%====Fourni====
deuxieme_etape(Abi,Abi1,Tbox) :-
	saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
	nl,write('Entrez le numero du type de proposition que vous voulez demontrer :'),nl,
	write('1 Une instance donnee appartient a un concept donne.'),nl,
	write('2 Deux concepts n"ont pas d"elements en commun(ils ont une intersection vide).'),nl, read(R), suite(R,Abi,Abi1,Tbox).
	
suite(1,Abi,Abi1,Tbox) :-
	write('Type 1 choisi !'),nl,acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :-
	acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(_,Abi,Abi1,Tbox) :-
	nl,write('Cette reponse est incorrecte.'),nl,
	saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).


% dernier([E],E).
% dernier([_|L],E) :- dernier(L,E).
% type_1_ok([X|L]) :- setof(U,iname(U),T), member(X,T), dernier(L,E),concept(E),nl,write("OK"),!.

type_1_ok([I,Y,C],I,C) :- setof(U,iname(U),T), member(I,T), Y = ':', concept(C),!.

convertC(cnamea(C),not(C)).
convertC(cnamena(C), not(X)) :- equiv(C,X). 

acquisition_prop_type1(Abi,Abi1,Tbox) :- lecture(L), type_1_ok(L,I,C),convertC(C,NewC),concat(Abi1,[nnf(NewC)],Abi1),write('on arrive'),!. 


lecture([X|L]):-
read(X),
write(X),nl,
X \= fin, !,
lecture(L).
lecture([]).
%=============

%Définition du prédicat concept = correction sémantique
concept(C) :- setof(X,cnamea(X),L),member(C,L). %Concept atomique
concept(not(C)) :- concept(C). %Négation
concept(or(C1,C2)) :- concept(C1),concept(C2). %Ou
concept(and(C1,C2)) :- concept(C1),concept(C2). %Et
concept(some(R,C)) :- concept(C),setof(X,rname(X),L),member(R,L). %Existe
concept(all(R,C)) :- concept(C),setof(X,rname(X),L),member(R,L). %Tous
concept(Ccplx) :- setof(X,cnamena(X),L),member(Ccplx,L). %Concept non-atomique
concept(I,C) :- setof(X,iname(X),L),member(Instance,L),concept(C). %Instance



%Mise sous nnf
%====Fourni====
nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)) :- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),X):-!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).
%==============

% Partie 3
%====Fourni====
troisieme_etape(Abi,Abr) :-
tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
resolution(Lie,Lpt,Li,Lu,Ls,Abr),
nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').
compteur(1).
%=============
