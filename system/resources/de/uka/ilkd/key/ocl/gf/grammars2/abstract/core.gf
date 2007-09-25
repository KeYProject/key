--# -path=.:resourceAbstract:prelude
abstract core = {
cat
	Class;	 
	Instance Class;
--	CoercedTo Class;
	Subtype (sub, super : Class);

	Constraints;
	Constraint;
	ClassConstraintBody;
	OperConstraintBody;
	
	
	ConstraintHideContext;
	ConstraintHCInvariant;

	VarSelf (c : Class);
	VarResult (c : Class);

	InstIter (iter, exp : Class);
	SentIter (iter : Class);
	CollList Class;

	Sent;
    	AtomSent ; -- negatable sentence
	
	LetDef Class;
	LetDefSent;
	LetDefList;
	
	InstNoType;
	
	Document;
	
    AndList;
    OrList;
    SumList;
    ProductList;
 
 --
 -- Properties
 --
    -- Properties represent the attributes/operations/associations of classes.
    -- The categories for properties are dependent types,
    -- so that they contain type information.
    -- E.g. for for a class Person with an integer attribute "age", 
    -- and a query "income(d:Date, c:Currency) : Integer", 
    -- we would get something like:
    -- Person_age_attr : Property Person Integer;
    -- Person_income_query : Instance Date -> Instance Currency -> Property Person Integer;

    Property Class Class;    
   
    -- Boolean and Is properties are special cases. They always return AtomSents,
    -- so no return type information is necessary. 
    Predicate Class;

    
fun	
	dropType : (c:Class) -> Instance c -> InstNoType;

	self : (c:Class) -> VarSelf c -> Instance c;
	result : (c:Class) -> VarResult c -> Instance c;
	
	atPre : (c:Class) -> Instance c -> Instance c;
	atPreSent : Sent -> Sent;

	oneConstraint : Constraint -> Constraints;
	consConstraint : Constraint -> Constraints -> Constraints;
	document : Constraints -> Document;	
	
	defC : (c:Class) -> LetDef c -> ClassConstraintBody -> ClassConstraintBody;
	defSentC : LetDefSent -> ClassConstraintBody -> ClassConstraintBody;
	invC : Sent -> ClassConstraintBody -> ClassConstraintBody;
	invCt : Sent -> ClassConstraintBody;
	emptyClassC : ClassConstraintBody;

	emptyOperC : OperConstraintBody;
	preC : Sent -> OperConstraintBody -> OperConstraintBody;
	postC : Sent -> OperConstraintBody -> OperConstraintBody;
	prepostCt : Sent -> Sent -> OperConstraintBody;
	emptyPostC : Sent;
	
	invHC : Sent -> ConstraintHCInvariant;
 
--  	subTypeRefl : (c : Class) -> Subtype c c;
--  	subTypeTrans : (a, b, c : Class) -> Subtype a b -> Subtype b c -> Subtype a c;
 	coerce : (sub,super:Class) -> Subtype sub super -> Instance sub -> Instance super;
 
	eq : (c:Class) -> (a,b : Instance c) -> Sent;
	neq : (c:Class) -> (a,b : Instance c) -> Sent;
	

--
-- Let definitions
--

fun 
-- this does not work in OCL because we have no implicit propcalls there:
--     letDef : (c:Class) -> (definiendum : Instance c) -> 
--         (definiens : Instance c) -> LetDef c;
--     letDefSent : (definiendum : Sent) -> (definiens : Sent) -> LetDefSent;


    letProperty : (rec,ret:Class) -> 
        (definiendum : Property rec ret) -> 
        (definiens : Instance ret) -> 
        LetDef ret;

    letPredicate : (rec:Class) -> 
        (definiendum : Predicate rec) -> 
        (definiens : Sent) -> 
        LetDefSent;

    letAddArg : (c,d:Class) -> (Instance c -> LetDef d) -> LetDef d;
    letAddArgSent : (c:Class) -> (Instance c -> LetDefSent) -> LetDefSent;

    -- to get parameter types in OCL linearization of letdefs:
    typeFormalParam : (c:Class) -> Instance c -> Instance c;

    nilLet : LetDefList;
    consLet : (c:Class) -> LetDef c -> LetDefList -> LetDefList;
    consLetSent : LetDefSent -> LetDefList -> LetDefList;

    -- let only allowed as top level expr, which always has type Sent:
    localLet : LetDefList -> Sent -> Sent; 

--
-- AtomSent
--
	posAtom : AtomSent -> Sent ;
    negAtom : AtomSent -> Sent ;

--
-- Calling Properties & Predicates
--
    propCall : (rec,ret:Class) -> Instance rec ->  Property rec ret  
        -> Instance ret;
    implPropCall : (rec,ret:Class) ->  Instance rec -> Property rec ret  
        -> Instance ret;

    predCall : (rec:Class) -> Instance rec -> Predicate rec -> AtomSent;
    implPredCall : (rec:Class) ->  Instance rec -> Predicate rec -> AtomSent;

{-
--
-- support 'aggregation' with lists of instances
--
cat InstList Class;

fun twoInst : (c:Class) -> (a,b : Instance c) -> InstList c;
    consInst : (c:Class) -> Instance c -> InstList c -> InstList c;
    
    instList2andInst : (c:Class) -> InstList c -> Instance c;
    instList2orInst  : (c:Class) -> InstList c -> Instance c;
-}
};

