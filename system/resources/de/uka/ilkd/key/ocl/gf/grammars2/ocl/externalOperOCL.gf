resource externalOperOCL = open Prelude, precedenceOCL, myTypesOCL in {

--lintype Inst = Inst0;

oper
	stdClass : Str -> {s:Str} = ss;
	contextOp00 : Str -> Str -> Str -> ConstraintL =
		\class, op, body -> ss ("context" ++ class ++ "::" ++ op ++ "()"  ++ body);
	contextOp01 : (class, op, ret, body : Str) -> ConstraintL =
		\class, op, ret, body -> ss ("context" ++ class ++ "::" ++ op ++ "()" ++ ":" ++ ret ++ body);
	contextOp10 : (class, op, args, body : Str) -> ConstraintL = 
		\class, op, args, body -> ss ("context" ++ class ++ "::" ++ op ++ "(" ++ args ++ ")" 
			++ body);
	contextOp11 : Str -> Str -> Str -> Str -> Str -> ConstraintL = 
		\class, op, args, ret, body -> ss ("context" ++ class ++ "::" ++ op ++ "(" ++ args ++ ")" 
			++ ":" ++ ret  ++ body);

	contextClass : Str -> Str -> ConstraintL = \class, body -> 
		ss ("context" ++ class ++ body);

	inst2str : Inst -> Str = \i -> case i.isAtpre of {
		True => i.s1;
		False => i.s0};

    mkAtPre : Inst -> Inst = \i -> {
        s0 = i.s0;
        s1 = i.s1;
        p = i.p;
        isAtpre = True
    };

	const : Str -> Inst = \f -> mkConst f (f ++ "@pre");
	postfix : Prec -> Str -> Inst -> Inst = \p, f, a -> 
	 	mkPostfix p f (f ++ "@pre") a ;
	prefix : Prec -> Str -> Inst -> Inst = \p, f, a->
	 	mkPrefix p f (f ++ "@pre") a;
	infix : Prec -> Str -> Inst -> Inst -> Inst = \p, f, a, b ->
	 	mkInfix p f (f ++ "@pre") a b;
	infixL : Prec -> Str -> Inst -> Inst -> Inst = \p, f, a, b ->
	 	mkInfixL p f (f ++ "@pre") a b;
	infixR : Prec -> Str -> Inst -> Inst -> Inst = \p, f, a, b ->
 	 	mkInfixR p f (f ++ "@pre") a b;

	argNil : ArgList = {s = ""; empty = True};
	argCons : Inst -> ArgList -> ArgList = 
		\x, xs -> {s = case xs.empty of {
			True => noParen x;
			False => xs.s ++ "," ++ noParen x
		}; empty = False};
	dotOper : Inst -> Str -> Str -> Inst = \obj, query, args -> { 
		s0 = (infixL dotP "." obj (const (query ++ "(" ++ args ++")"))).s0;
		s1 = (infixL dotP "." obj (const (query ++ "@pre" ++ "(" ++ args ++")"))).s0;
		isAtpre = False;
		p = dotP};
	arrowOper : Inst -> Str -> Str -> Inst = \obj, query, args -> { 
		s0 = (infixL dotP "->" obj (const (query ++ "(" ++ args ++")"))).s0;
		s1 = (infixL dotP "->" obj (const (query ++ "@pre" ++ "(" ++ args ++")"))).s0;
		isAtpre = False;
		p = dotP};
	dotAssoc : Inst -> Str -> Inst = \obj, assoc -> { 
		s0 = (infixL dotP "." obj (const assoc )).s0;
		s1 = (infixL dotP "." obj (const (assoc ++ "@pre"))).s0;
		isAtpre = False;
		p = dotP};
	dotOper0 : Inst -> Str -> Inst = \obj, query -> {
		s0 = (infixL dotP "." obj (const (query ++ "()"))).s0;
		s1 = (infixL dotP "." obj (const (query ++ "@pre" ++ "()"))).s0;
		isAtpre = False;
		p = dotP};
	dotOper1 : Inst -> Str -> Inst -> Inst = \obj, query, arg -> {
		s0 = (infixL dotP "." obj (const (query ++ "(" ++ noParen arg ++ ")"))).s0;
		s1 = (infixL dotP "." obj (const (query ++ "@pre" ++ "(" ++ noParen arg ++ ")"))).s0;
		isAtpre = False;
		p = dotP};
	arrowOper0 : Inst -> Str -> Inst = \obj, query -> {
		s0 = (infixL dotP "->" obj (const (query ++ "()"))).s0;
		s1 = (infixL dotP "->" obj (const (query ++ "@pre" ++ "()"))).s0;
		isAtpre = False;
		p = dotP};
	arrowOper1 : Inst -> Str -> Inst -> Inst = \obj, query, arg -> {
		s0 = (infixL dotP "->" obj (const (query ++ "(" ++ noParen arg ++ ")"))).s0;
		s1 = (infixL dotP "->" obj (const (query ++ "@pre" ++ "(" ++ noParen arg ++ ")"))).s0;
		isAtpre = False;
		p = dotP};		
	dotAttr : Inst -> Str -> Inst = \a,s -> {
		s0 = (infixL dotP "." a (const s)).s0;
		s1 = (infixL dotP "." a (const (s ++ "@pre"))).s0;
		isAtpre = False;
		p = dotP};
	arrowAttr : Inst -> Str -> Inst = \a,s -> {
		s0 = (infixL dotP "->" a (const s)).s0;
		s1 = (infixL dotP "->" a (const (s ++ "@pre"))).s0;
		isAtpre = False;
		p = dotP};

	mkQuery : Inst -> Str -> ArgList -> Inst = \obj, query, args -> 
		dotOper obj query args.s;

	
	
	-- new operations only used in generated grammars:
	-- PropL will be the lincat of all the various property types
	PropL : Type = {s0 : Str; s1 : Str; s2 : Str};  
	-- s0 is the prop identifier, s1 is dot or arrow, s2 contains the arguments (if any)
	propAttr : Str -> PropL = \s -> {s0 = s; s1 = "."; s2 = ""};
	propAssoc : Str -> PropL = \s -> {s0 = s; s1 = "."; s2 = ""};
	propWithArgs : Str -> ArgList -> PropL = \s,args -> 
	   {s0 = s; s1 = "."; s2 = "(" ++ args.s ++ ")"};
	-- applyProp will be used by all "property call funs", 
	-- e.g. useSimpleProp, useComplexProp, etc etc
	applyProp : PropL -> Inst -> Inst = \prop, obj -> {
		s0 = (infixL dotP prop.s1 obj (const (prop.s0 ++ prop.s2 ))).s0;
		s1 = (infixL dotP prop.s1 obj (const (prop.s0 ++ "@pre" ++ prop.s2))).s0;
		isAtpre = False;
		p = dotP};
	applyPropImpl : PropL -> Inst -> Inst = \prop, _ -> mkConst 
	   (prop.s0 ++ prop.s2) (prop.s0 ++ "@pre" ++ prop.s2);



-- From oclLibrary.OCL.gf
oper wrapIter : {s1, s2, s3 :Str} -> Str = \i -> (
		i.s1 ++ i.s2 ++ "|" ++ i.s3);  -- with type info (i.s2)


-- collection literals
    emptyColl : Str -> Inst = \coll -> const (coll ++ "{" ++ "}");
    singletonColl : Str -> Inst -> Inst = \coll, x -> const (coll ++  "{" ++ inst2str x ++ "}");
    listAsColl : Str -> Str -> Inst = \coll, xs -> const (coll ++ "{" ++ xs ++ "}");
    rangeAsColl : Str -> Inst -> Inst -> Inst = \coll, f, t -> 
        const (coll ++ "{" ++ usePrec f unP ++ ".." ++ usePrec t unP ++ "}");

-- let-definitions
oper letNoArg : ClassL -> PropL -> Inst -> LetDefL = \ret, prop, definiens -> {
        s0 = prop.s0 ++ prop.s2;
        s1 = inst2str definiens
    };

    mkEnum : Str -> ClassL = \str -> stdClass str;
    enumVal : Str -> Inst = const;

};
