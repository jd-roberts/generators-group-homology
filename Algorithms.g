#GAP code

LoadPackage("kbmag");;

######################
#Presentation of a finite group
#Output: [Isomorphic Fp Group, Free Group, Relators]
PresentationOfFiniteGroup:=function(FiniteGroup)

local Pres, Group, Freegroup, Relators, group;

Pres:=PresentationViaCosetTable(FiniteGroup);
TzGoGo(Pres);
Group:=FpGroupPresentation(Pres);
Freegroup:=FreeGroupOfFpGroup(Group);
Relators:=RelatorsOfFpGroup(Group);

group:=Freegroup/Relators;

return[group,Freegroup,Relators];
end;;

###########################
#Simplified Presenation of a Fp Group
#Output: [("smaller") Isomorphic Fp group, Free Group, Relators]
PresentationOfFpGroup:=function(FpGroup)

local iso, range, Group, Freegroup, Relators;


iso:=IsomorphismSimplifiedFpGroup(FpGroup);
range:=Range(iso);
Group:=range;
Freegroup:=FreeGroupOfFpGroup(range);
Relators:=RelatorsOfFpGroup(range);


return[iso,Group,Freegroup,Relators];
end;;

##############################################
#Input: Free group, relators, prime p 
#Output: Dimension of H_1(F/R,F_p) <=> F/R \otimes F_p provided F/R is abelian

FirstHomologyCoefficicents:=function(Freegroup,Relators,Prime)
local AbelInv, list, x;
AbelInv:=AbelianInvariants(Freegroup/Relators);
list:=[];
for x in AbelInv do
	if x mod Prime = 0 then Add(list,x);
	fi;
	od;
return Size(list);
end;;


##############################################
#Input: Free group, relators, prime p
#Output: Dimension of Tor(H_1(G),F_p)

Tor:=function(Freegroup,Relators,Prime)
local AbelInv, list1, list2, x;
AbelInv:=AbelianInvariants(Freegroup/Relators);
list1:=[];
list2:=[];
for x in AbelInv do
     if x<>0 then Add(list1,x);
     fi;
     od;
for x in list1 do
     if x mod Prime = 0 then Add(list2,1);
     fi;
     od;
return Sum(list2);
end;;

###############################################
#P-Primary Rank
#Output: P-Primary Rank of Fp Group

PrimePrimaryRank:=function(Freegroup,Relators,Prime)
local AbelInv, list1, list2, x;
AbelInv:=AbelianInvariants(Freegroup/Relators);
list1:=[];
list2:=[];
for x in AbelInv do
     if x <> 0 then Add(list1,x);
     fi;
     od;
for x in list1 do
     if x mod Prime = 0 then Add(list2,PadicValuation(x,Prime));
     fi;
	     od;
return Sum(list2);	
end;;

###############################################
#The (special) Word Problem
#Output: Reduced word

Reduce_Word:=function(Freegroup,Relators,TestWord,Sublist,Prime)
local Rel_P, GroupGen, comm, G, RG, OR;

Rel_P:=List(Relators,x->x^Prime);
GroupGen:=GeneratorsOfGroup(Freegroup);
comm:=ListX(GroupGen,Relators,Comm);

G:=Freegroup/Concatenation(comm,Rel_P,Sublist);
RG:=KBMAGRewritingSystem(G);
OR:=OptionsRecordOfKBMAGRewritingSystem(RG);
OR.maxeqns:=500000;
OR.tindyint:=100;
MakeConfluent(RG);

return ReducedWord(RG,TestWord);
end;;

#################################################
#Attempts to reduce a generating set
#Output: List of generators

FindBasis:=function(Freegroup,Relators,Prime,Sublist)
local Gen,TestWord,x,list; 
Gen:=Sublist;
list:=[];
for x in Sublist do 
     TestWord:=Reduce_Word(Freegroup,Relators,x,Difference(Gen,[x]),Prime);
		Add(list,TestWord);
        if IsOne(TestWord)=true then Gen:=Difference(Gen,[x]);
        fi;
        od;
return [Gen,Size(Gen),list];
end;;

#######################################################
#Gives the estimate for H_2
#Output: Upper bound on dimension of H_2
SecondHomologyCoefficients:=function(Freegroup, Relators, Prime, Sublist)

local a,b,c,d,e,f,ff,RPrime;

f:=GeneratorsOfGroup(Freegroup);
ff:=ListX(f,f,Comm);
RPrime:=List(Relators,x->x^Prime);

a:=Tor(Freegroup,Relators,Prime);
b:=PrimePrimaryRank(Freegroup,Concatenation(Relators,ff),Prime);
c:=PrimePrimaryRank(Freegroup,Concatenation(RPrime,ff),Prime);
e:=FindBasis(Freegroup,Relators,Prime,Sublist);
d:=a+b-c+e[2];
return [e[1],d,e[3]];
end;;



###############################################
#The (special) Word Problem (large parameters)
#Output: Reduced word

Reduce_Word2ndHom_large:=function(Freegroup,Relators,TestWord,Sublist,Prime)

local Rel_P, GroupGen, comm, G, RG, OR;

Rel_P:=List(Relators,x->x^Prime);
GroupGen:=GeneratorsOfGroup(Freegroup);
comm:=ListX(GroupGen,Relators,Comm);

G:=Freegroup/Concatenation(comm,Rel_P,Sublist);
RG:=KBMAGRewritingSystem(G);
OR:=OptionsRecordOfKBMAGRewritingSystem(RG);
OR.maxeqns:=10000000;
OR.tindyint:=1000;
MakeConfluent(RG);

return ReducedWord(RG,TestWord);
end;;

#################################################
#Attempts to reduce a generating set (large parameters)
#Output: List of generators

FindBasis2ndHom_large:=function(Freegroup,Relators,Prime,Sublist)

local Gen,TestWord,x,set1; 

set1:=[];
Gen:=Sublist;

for x in Sublist do TestWord:=Reduce_Word2ndHom_large(Freegroup,Relators,x,Difference(Gen,[x]),Prime);
	Add(set1,TestWord);
	if IsOne(TestWord)=true then Gen:=Difference(Gen,[x]);
	fi;
	od;
return [Gen, Size(Gen), set1];
end;;

##################################################
#Gives the estimate for H_2 (large parameters)
#Output: Upper bound on dimension of H_2
SecondHomologyCoefficients_large:=function(Freegroup, Relators, Prime, Sublist)

local a,b,c,d,e,f,ff,RPrime;



f:=GeneratorsOfGroup(Freegroup);
ff:=ListX(f,f,Comm);
RPrime:=List(Relators,x->x^Prime);

a:=Tor(Freegroup,Relators,Prime);
b:=PrimePrimaryRank(Freegroup,Concatenation(Relators,ff),Prime);
c:=PrimePrimaryRank(Freegroup,Concatenation(RPrime,ff),Prime);
e:=FindBasis2ndHom_large(Freegroup,Relators,Prime,Sublist);
d:=a+b-c+e[2];
return [e[1],d,e[3]];
end;;

#################################################
