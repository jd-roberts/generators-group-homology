# Reference word lists transcribed from the user-supplied Anton 0804.3553v1.
# Section 7, pp. 19-21. Comparison fixture only; no group completion.
# PDF SHA256: 47aa5ce2ac126f52e751992d17aeafab7a8680e6cd92bf62b90293d98569a1b7

AntonPaperR3 := function(F)
local z,u1,a,b,b0,b1,b2,w;

z:=F.1;; u1:=F.2;; a:=F.3;; b:=F.4;; b0:=F.5;; b1:=F.6;; b2:=F.7;; w:=F.8;;

return [
b0^-1*b*a,
b1^-1*z*b*z*a,
b2^-1*z^2*b*z^2*a,
w^-1*z*u1,
z^3, z*u1*z^-1*u1^-1,
a^4, a^2*z*a^-2*z^-1,
a^2*u1*a^-2*u1^-1,
z*a*z*a^-1,
u1*a*u1*a^-1,
b0*b1*b0^-1*b1^-1,
b0*b2*b0^-1*b2^-1,
b1*b2*b1^-1*b2^-1,
b^3*a^-2, b0*b1*b2*a^-2,
b0^-3*w^-1*b0^-1*w,
b1^-3*w^-1*b1^-1*w,
b2^-3*w^-1*b2^-1*w,
(b0*b1^-1*a^-1*u1)^3,
a^2*b^-1*u1*b*z^2*b^-1*b0^-1*z*b*z^2*u1
];
end;;

AntonPaperR5 := function(F)
local z,u1,u2,a,b,b0,b1,b2,b3,b4,w;

z:=F.1;; u1:=F.2;; u2:=F.3;; a:=F.4;; b:=F.5;; b0:=F.6;; b1:=F.7;; b2:=F.8;; b3:=F.9;; b4:=F.10;; w:=F.11;;

return [
b0^-1*b*a,
b1^-1*z^2*b*z^2*a,
b2^-1*z^4*b*z^4*a,
b3^-1*z*b*z*a,
b4^-1*z^3*b*z^3*a,
w^-1*z*u1*u2,
z^5, z*u1*z^-1*u1^-1,
z*u2*z^-1*u2^-1,
u1*u2*u1^-1*u2^-1,
a^4, a^2*z*a^-2*z^-1,
a^2*u1*a^-2*u1^-1,
a^2*u2*a^-2*u2^-1,
z*a*z*a^-1,
u1*a*u1*a^-1,
u2*a*u2*a^-1,
b0*b1*b0^-1*b1^-1,
b0*b2*b0^-1*b2^-1,
b0*b3*b0^-1*b3^-1,
b0*b4*b0^-1*b4^-1,
b1*b2*b1^-1*b2^-1,
b1*b3*b1^-1*b3^-1,
b1*b4*b1^-1*b4^-1,
b2*b3*b2^-1*b3^-1,
b2*b4*b2^-1*b4^-1,
b3*b4*b3^-1*b4^-1,
b^3*a^-2, b0*b1*b2*b3*b4*a^-2,
b0^-5*w^-1*b0*w,
b1^-5*w^-1*b1*w,
b2^-5*w^-1*b2*w,
b3^-5*w^-1*b3*w,
b4^-5*w^-1*b4*w,
(b0*b1^-1*a^-1*u1)^3,
(b0*b2^-1*a^-1*u2)^3,
(b0*b1^-1*b2^-1*b3*a^-1*u1*u2)^3,
a^2*b^-1*u1*b*z^3*b^-1*b0^-1*z^2*b*z^4*u1,
a^2*b^-1*u2*b*z*b^-1*b0^-1*z^4*b*z^3*u2
];
end;;
