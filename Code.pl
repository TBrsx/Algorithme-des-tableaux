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
recup(X) :- findall((michelAnge,X),instR(michelAnge,X,aCree),X).

premiere_etape(Tbox,Abi,Abr):- tbox(Tbox),!,abi(Abi),!,abr(Abr),!.
	
% Partie 2
%====Fourni====
deuxieme_etape(Abi,Abi1,Tbox) :-
	saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
	nl,write('Entrez le numero du type de proposition que vous voulez demontrer :'),nl,
	write('1 Une instance donnee appartient a un concept donne.'),nl,
	write("2 Deux concepts n'ont pas d'elements en commun(ils ont une intersection vide)."),nl, read(R), suite(R,Abi,Abi1,Tbox),!.
	
suite(1,Abi,Abi1,Tbox) :-
	write('Type 1 choisi !'),nl,acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :-
	acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(_,Abi,Abi1,Tbox) :-
	nl,write('Cette reponse est incorrecte.'),nl,
	saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

%=============

%Définition du prédicat concept = correction sémantique
concept(C) :- setof(X,cnamea(X),L),member(C,L). %Concept atomique
concept(not(C)) :- concept(C). %Négation
concept(or(C1,C2)) :- concept(C1),concept(C2). %Ou
concept(and(C1,C2)) :- concept(C1),concept(C2). %Et
concept(some(R,C)) :- concept(C),setof(X,rname(X),L),member(R,L). %Existe
concept(all(R,C)) :- concept(C),setof(X,rname(X),L),member(R,L). %Tous
concept(Ccplx) :- setof(X,cnamena(X),L),member(Ccplx,L). %Concept non-atomique
concept(I,C) :- setof(X,iname(X),L),member(I,L),concept(C). %Instance



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

%Vérifie que l'entrée type 1 est correcte
type_1_ok([I,C],I,C) :- setof(U,iname(U),T), member(I,T), concept(C),!.

%Décompexifie récursivement les concepts donnés en entrée
decomplexe(C,X):- equiv(C,X).
decomplexe(C,C) :- cnamea(C).
decomplexe(or(C1,C2),X) :- X = or(Y,Z),decomplexe(C1,Y),decomplexe(C2,Z).
decomplexe(and(C1,C2),X) :- X = and(Y,Z),decomplexe(C1,Y),decomplexe(C2,Z).
decomplexe(some(R,C),X) :- X = some(R,Y),decomplexe(C,Y).
decomplexe(all(R,C),X) :- X = all(R,Y),decomplexe(C,Y).
decomplexe(not(C),X) :- X = not(Y), decomplexe(C,Y).

%Acquisition type 1
acquisition_prop_type1(Abi,Abi1,_) :- lecture(L), type_1_ok(L,I,C),decomplexe(C,NewC),!,nnf(not(NewC),NotnewC),concat(Abi,[(I,NotnewC)],Abi1),nl,write("On montre l'insatisfiabilité de "),write(NotnewC). 



% Partie 3
%====Fourni====
troisieme_etape(Abi,Abr) :-
nl,nl,write("Troisième étape"),nl,
tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
nl,write("Lie"),write(Lie),
nl,write("Lpt"),write(Lpt),
nl,write("Li"),write(Li),
nl,write("Lu"),write(Lu),
nl,write("Ls"),write(Ls),
resolution(Lie,Lpt,Li,Lu,Ls,Abr),
nl,write('Youpiiiiii, on a démontré la proposition initiale !!!').
compteur(1).

%=============

%Tri

tri_Abox([(I,some(R,C))|Q],[(I,some(R,C))|Lie],Lpt,Li,Lu,Ls) :- tri_Abox(Q,Lie,Lpt,Li,Lu,Ls).
	
tri_Abox([(I,all(R,C))|Q],Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls) :- tri_Abox(Q,Lie,Lpt,Li,Lu,Ls).
	
tri_Abox([(I,and(C1,C2))|Q],Lie,Lpt,[(I,and(C1,C2))|Li],Lu,Ls) :- tri_Abox(Q,Lie,Lpt,Li,Lu,Ls).
	
tri_Abox([(I,or(C1,C2))|Q],Lie,Lpt,Li,[(I,or(C1,C2))|Lu],Ls) :- tri_Abox(Q,Lie,Lpt,Li,Lu,Ls).
	
tri_Abox([T|Q],Lie,Lpt,Li,Lu,[T|Ls]) :- tri_Abox(Q,Lie,Lpt,Li,Lu,Ls).

tri_Abox([],[],[],[],[],[]).

%Règles de résolution

complete_some(Lie,_,_,_,_,Abr):- 
complete_some([],_,_,_,_,[]). 


% Utilitaires fournis

concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).

genere(Nom) :- compteur(V),nombre(V,L1),
	concat([105,110,115,116],L1,L2),
	V1 is V+1,
	dynamic(compteur/1),
	retract(compteur(V)),
	dynamic(compteur/1),
	assert(compteur(V1)),nl,nl,nl,
	name(Nom,L2).
nombre(0,[]).
nombre(X,L1) :-
	R is (X mod 10),
	Q is ((X-R)//10),
	chiffre_car(R,R1),
	char_code(R1,R2),
	nombre(Q,L),
	concat(L,[R2],L1).
chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').

lecture([X|L]):-
read(X),
write(X),nl,
X \= fin, !,
lecture(L).
lecture([]).


