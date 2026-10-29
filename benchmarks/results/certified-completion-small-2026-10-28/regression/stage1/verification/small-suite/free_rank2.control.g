Read("Algorithms.g");;
(function()
 local f,r,words,answer,a,t;
 f:=FreeGroup(2);
 words:=function(xs) return Product(xs,x->f.(AbsInt(x))^SignInt(x)); end;
 r:=List([],words);
 answer:=SecondHomologyCoefficients(f,r,3,r);
 a:=Tor(f,r,3);
 if IsEmpty(r) then t:=0; else
 t:=RankMat(List(r,w->List(GeneratorsOfGroup(f),g->ExponentSumWord(w,g)))); fi;
 Print("SPAN_CONTROL ",answer[2]," GAP ",GAPInfo.Version,
       " KBMAG ",PackageInfo("kbmag")[1].Version," Tor ",a," rank ",t,"\n");
 if answer[2]<>0 or a<>0 or t<>0 then Error("known small control bound mismatch"); fi;
end)();
QUIT;
