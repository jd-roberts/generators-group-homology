Read("Algorithms.g");;
(function()
 local f,r,words,answer,a,t;
 f:=FreeGroup(2);
 words:=function(xs) return Product(xs,x->f.(AbsInt(x))^SignInt(x)); end;
 r:=List([[1, 1], [2, 2], [-1, -2, 1, 2]],words);
 answer:=SecondHomologyCoefficients(f,r,2,r);
 a:=Tor(f,r,2);
 if IsEmpty(r) then t:=0; else
 t:=RankMat(List(r,w->List(GeneratorsOfGroup(f),g->ExponentSumWord(w,g)))); fi;
 Print("SPAN_CONTROL ",answer[2]," GAP ",GAPInfo.Version,
       " KBMAG ",PackageInfo("kbmag")[1].Version," Tor ",a," rank ",t,"\n");
 if answer[2]<>3 or a<>2 or t<>2 then Error("known small control bound mismatch"); fi;
end)();
QUIT;
