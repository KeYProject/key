resource precedenceOCL = open Prelude in {

-- precedence parameters and operations adapted to the OCL grammars
-- which use {s0, s1 : Str} as the starting point for the linearization 
-- type of expressions.


--lintype PrecTerm = {s : Prec => Str};
--lintype PrecInh = {s0, s1 : Str; p : Prec; isAtpre : Bool};
oper
    PrecTerm : Type = {s : Prec => Str};
    PrecInh : Type = {s0, s1 : Str; p : Prec; isAtpre : Bool};

param Prec = p11 | p10 | p9 | p8 | p7 | p6 | p5 | p4 | p3 | p2 | p1;

--
-- OCL precedences:
--
oper atpreP : Prec = p10;
    dotP : Prec = p9;   -- .  ->
    unP : Prec = p8;   -- unary 'not' and '-'
    multP : Prec = p7;
    addP : Prec = p6;
    ifP : Prec = p5; -- if then else endif
    gtP : Prec = p4; -- < > <= >=
    eqP : Prec = p3; -- = <>
    andP : Prec = p2; -- and or xor
    impP : Prec = p1; -- implies

--
-- basic precedence definitions
--

oper nextPrec : Prec => Prec = 
	table {p1 => p2; p2 => p3; p3 => p4; p4 => p5; p5 => p6;
		p6 => p7; p7 => p8; p8 => p9; p9 => p10; p10 => p11; p11 => p11};  -- note p11 => p11

oper mkParenth : Str -> Str  = \str -> "(" ++ str ++ ")";
  
oper mkPrec : Str -> Prec => Prec => Str = \s ->
	let {ps:Str = mkParenth s} in
	table {
	p11 => table {
		_ => s};   -- highest priority, no par.
	p10 => table {
		p11 => ps;
		_ => s};
	p9 => table {
		p11 => ps;
		p10 => ps;
		_ => s};
	p8 => table {
		p11 => ps;
		p10 => ps;
		p9 => ps;
		_ => s};
	p7 => table {
		p11 => ps;
		p10 => ps;
		p9 => ps;
		p8 => ps;
		_ => s};
	p6 => table {
		p11 => ps;
		p10 => ps;
		p9 => ps;
		p8 => ps;
		p7 => ps;
		_ => s}; 
	p5 => table {
		p5 => s;
		p4 => s;
		p3 => s;
		p2 => s;
		p1 => s;
		_ => ps};
	p4 => table {
		p4 => s;
		p3 => s;
		p2 => s;
		p1 => s;
		_ => ps};		 
	p3 => table {
		p3 => s;
		p2 => s;
		p1 => s;
		_ => ps};
	p2 => table {
		p2 => s;
		p1 => s;
		_ => ps};
	p1 => table {
		p1 => s;    -- lowest, without parens only in this case
		_ => ps}
	};



--
-- precedence via tables:
-- 



oper mkConst' : Str -> PrecTerm =
	\c -> {s = mkPrec c ! p11};
    
    mkInfix' : Prec -> Str -> PrecTerm -> PrecTerm -> PrecTerm =
	\p, f, x, y -> 
	let {pp : Prec = nextPrec ! p} 
	in {s = mkPrec (x.s!pp ++ f ++ y.s!pp) ! p};

    mkInfixL' : Prec -> Str -> PrecTerm -> PrecTerm -> PrecTerm =
	\p, f, x, y ->
	{s = mkPrec (x.s!p ++ f ++ y.s!(nextPrec ! p)) ! p};
    mkInfixR' : Prec -> Str -> PrecTerm -> PrecTerm -> PrecTerm =
	\p, f, x, y ->
	{s = mkPrec (x.s!(nextPrec ! p) ++ f ++ y.s!p) ! p};






--
-- for precedence as inherent feature
--


oper usePrec : PrecInh -> Prec -> Str =
	\x, p -> case x.isAtpre of {
		False => mkPrec x.s0 ! x.p ! p;
		True => mkPrec x.s1 ! x.p ! p
	};


oper noParen : PrecInh -> Str = \x -> usePrec x p1;


oper mkConst : Str -> Str -> PrecInh =
	\c, cAtpre -> {s0 = c; s1 = cAtpre; p = p11; isAtpre = False};

oper mkInfix : Prec -> Str -> Str -> PrecInh -> PrecInh -> PrecInh =
	\p, f, fAtpre, x, y -> {
		s0 = usePrec x (nextPrec ! p) ++ f ++ usePrec y (nextPrec ! p);
		s1 = usePrec x (nextPrec ! p) ++ fAtpre ++ usePrec y (nextPrec ! p);
		p = p;
		isAtpre = False
	};

oper mkInfixL : Prec -> Str -> Str -> PrecInh -> PrecInh -> PrecInh =
	\p, f, fAtpre, x, y -> {
		s0 = usePrec x p ++ f ++ usePrec y (nextPrec ! p);
		s1 = usePrec x p ++ fAtpre ++ usePrec y (nextPrec ! p);
		p = p;
		isAtpre = False
	};

oper mkInfixR : Prec -> Str -> Str -> PrecInh -> PrecInh -> PrecInh =
	\p, f, fAtpre, x, y -> {
		s0 = usePrec x (nextPrec ! p) ++ f ++ usePrec y p;
		s1 = usePrec x (nextPrec ! p) ++ fAtpre ++ usePrec y p;
		p = p;
		isAtpre = False
	};

oper mkPostfix : Prec -> Str -> Str -> PrecInh -> PrecInh =
	\p,f, fAtpre, x -> {
		s0 = usePrec x (nextPrec ! p) ++ f;
		s1 = usePrec x (nextPrec ! p) ++ fAtpre;
		p = p;
		isAtpre = False
	};
	
oper mkPrefix : Prec -> Str -> Str -> PrecInh -> PrecInh =
	\p,f, fAtpre, x -> {
		s0 = f ++ usePrec x (nextPrec ! p);
		s1 = fAtpre ++ usePrec x (nextPrec ! p);
		p = p;
		isAtpre = False
	};
	
};
