%!! Penser à charger ABox et Tbox

%Démarrage du programme
programme :-
	premiere_etape(Tbox,Abi,Abr),
	deuxieme_etape(Abi,Abi1,Tbox),
	troisieme_etape(Abi1,Abr).

%Partie 1 - abi : ABox assertions de concept, abr : Abox assertions de roles

%Pour afficher pour tester la lecture
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

%Décomplexifie récursivement les concepts donnés en entrée
decomplexe(C,X):- equiv(C,X). %Concept complexe
decomplexe(C,C) :- cnamea(C). %Concept atomique, pas besoin de décomplexer
decomplexe(or(C1,C2),X) :- X = or(Y,Z),decomplexe(C1,Y),decomplexe(C2,Z). %Ou
decomplexe(and(C1,C2),X) :- X = and(Y,Z),decomplexe(C1,Y),decomplexe(C2,Z). %And
decomplexe(some(R,C),X) :- X = some(R,Y),decomplexe(C,Y). %Existe
decomplexe(all(R,C),X) :- X = all(R,Y),decomplexe(C,Y). %Pour tout
decomplexe(not(C),X) :- X = not(Y), decomplexe(C,Y). % Non(Concept))

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
nl,write("Abr"),write(Abr),
resolution(Lie,Lpt,Li,Lu,Ls,Abr),
nl,write('Youpiiiiii, on a démontré la proposition initiale !!!').

%=============

%Tri

tri_Abox([(I,some(R,C))|Q],[(I,some(R,C))|Lie],Lpt,Li,Lu,Ls) :- 
	tri_Abox(Q,Lie,Lpt,Li,Lu,Ls). %Existe
	
tri_Abox([(I,all(R,C))|Q],Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls) :- 
	tri_Abox(Q,Lie,Lpt,Li,Lu,Ls). %Pour tout
	
tri_Abox([(I,and(C1,C2))|Q],Lie,Lpt,[(I,and(C1,C2))|Li],Lu,Ls) :- 
	tri_Abox(Q,Lie,Lpt,Li,Lu,Ls). %Et
	
tri_Abox([(I,or(C1,C2))|Q],Lie,Lpt,Li,[(I,or(C1,C2))|Lu],Ls) :- 
	tri_Abox(Q,Lie,Lpt,Li,Lu,Ls). %Ou
	
tri_Abox([T|Q],Lie,Lpt,Li,Lu,[T|Ls]) :- tri_Abox(Q,Lie,Lpt,Li,Lu,Ls). %Atome

tri_Abox([],[],[],[],[],[]).


resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- complete_some(Lie,Lpt,Li,Lu,Ls,Abr).

%Règles de résolution

complete_some([(I,(R,C))|Q],Lpt,Li,Lu,Ls,Abr):- 
	evolue((I,(R,C)),[(I,(R,C)),Q],Lpt,Li,Lu,Ls,Lie1, Lpt1, Li1, Lu1, Ls1,Abr,Abr1). %Si on trouve une règle existe
complete_some([],Lpt,Li,Lu,Ls,Abr) :- transformation_and([],Lpt,Li,Lu,Ls,Abr). %Si on n'en trouve pas

%Évolution

evolue((I,some(R,C)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1,Abr,Abr1) :-
	genere(Nom),!,concat([(I,Nom,R)],Abr,Abr1),%Ajout du rôle
	enleve((I,some(R,C)),Lie1,Lie1), %Supprime la règle itérée
	concat([(Nom,C)],Ls,Ls1),%Ajout de l'instance
	affiche_evolution_Abox(Ls, Lie, Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1).
	%Clash ?

evolue((I,all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1,Abr,Abr1) :- concat([(I,all(R,C))],Lpt,Lpt1).

evolue((I,and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1,Abr,Abr1) :- concat([(I,and(C1,C2))],Li,Li1).

evolue((I,or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1,Abr,Abr1) :- concat([(I,or(C1,C2))],Lu,Lu1).

evolue(A, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1,Abr) :-
concat([A],Ls,Ls1).


% Affichage
affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
nl,write("============ Abi avant règle ============"),nl,
ecrire_ls(Ls1),
ecrire_lie(Lie1),
ecrire_lu(Lu1),
ecrire_lpt(Lpt1),
ecrire_li(Li1),
ecrire_abr(Abr1),
nl,write("============ Abi après règle ============"),nl,

ecrire_abr(Abr2).


ecrire_ls([(I,C)]) : write(I),write(":"),write(C),nl,ecrire_ls(Q).
ecrire_ls([]).
ecrire_ls([(I,not(C))]) : write(I),write(":"),write(C),nl,ecrire_ls(Q).
ecrire_ls([]).


ecrire_abr([(A,B,R)|Q]) :- write("<"),write(A),write(","),write(B),write(">"),write(":"),write(R),nl,ecrire_abr(Q).
ecire_abr([]).



% Utilitaires fournis

concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).

compteur(1).

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


