%!! Penser à charger ABox et Tbox

%Démarrage du programme
programme :-
	premiere_etape(Tbox,Abi,Abr).
	%deuxieme_etape(Abi,Abi1,Tbox),
	%troisieme_etape(Abi1,Abr).

%Partie 1 - abi : ABox assertions de concept, abi1 : Abox assertions de roles


tbox(Tbox) :- findall((C,CG),(equiv(C,CG)),Tbox).
abi(Abi) :- findall((I,C),(inst(I,C)),Abi).
abr(Abr) :- findall((I,I2,R),(instR(I,I2,R)),Abir).



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
	acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :-
	acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(R,Abi,Abi1,Tbox) :-
	nl,write('Cette reponse est incorrecte.'),nl,
	
saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).
%=============

concept(anything).
concept(nothing).

lecture([X|L]):-
	read(X),
	X \= fin, !,
	lecture(L).
lecture([]).


% Partie 3
%====Fourni====
troisieme_etape(Abi,Abr) :-
tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
resolution(Lie,Lpt,Li,Lu,Ls,Abr),
nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').
compteur(1).
%=============
