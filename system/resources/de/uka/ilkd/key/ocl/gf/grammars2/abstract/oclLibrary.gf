--# -path=.:resourceAbstract:prelude
abstract oclLibrary = core ** {

--from the GF 1.2 core:
fun
	bool2sent : Instance BooleanC -> Sent;
	sent2bool : Sent -> Instance BooleanC;

----------------------------------------------
-- OCL Library classes
----------------------------------------------

--
-- 'ideomatic expressions', recurring patterns in OCL specs:
--

    -- these should really work on property calls (not on arbitrary
    -- expressions), but it is much simpler this way:
    decremented : Instance RealC -> Instance RealC -> AtomSent;
    incremented : Instance RealC -> Instance RealC -> AtomSent;
    notChanged : (c:Class) -> Instance c -> AtomSent;


--
-- KeY extensions
--
fun NullC : Class;
    nullConforms2 : (c:Class) -> Subtype NullC c; 
    null : Instance NullC;
    
    excThrown : (c:Class) -> Instance OclAnyC -> Instance c -> AtomSent;

--
-- OclType. Would it be better to just have Class? Apparently not.
--
fun OclTypeC : Class; -- could try to have OclTypeC : Class -> Class ???
    OclTypeCConforms2OclTypeC : Subtype OclTypeC OclTypeC;

-- this is not part of OCL:
fun class2oclType : Class -> Instance OclTypeC;
    class2name : Class -> Instance OclTypeC;

    otName : Instance OclTypeC -> Instance StringC;
    otAttributes : Instance OclTypeC -> Instance (Set StringC);
    otOperations : Instance OclTypeC -> Instance (Set StringC);
    otSupertypes : Instance OclTypeC -> Instance (Set OclTypeC);
    otAllSupertypes : Instance OclTypeC -> Instance (Set OclTypeC);
    otAllInstancesStrict : (c:Class) -> Instance OclTypeC -> Instance (Set c); -- Note extra Class argument!
    -- (compos. of allinst and evalType)

--
-- OclAny
--

fun OclAnyC : Class;
    conforms2OclAny : (c:Class) -> Subtype c OclAnyC;

-- might be better to define these for all classes (the class being a parameter)?
    anyOclIsKindOf : Instance OclAnyC -> Instance OclTypeC -> Sent;
    anyOclIsTypeOf : Instance OclAnyC -> Instance OclTypeC -> Sent;    
    anyOclAsTypeStrict : (c:Class) -> Instance OclAnyC -> Instance OclTypeC -> Instance c; -- N.B.
    anyOclInState : Instance OclAnyC -> Instance OclStateC -> Sent;
    anyOclIsNew : Instance OclAnyC -> Sent;



--
-- OclState
--
fun OclStateC : Class;
    OclStateCConforms2OclStateC : Subtype OclStateC OclStateC;




--
-- Bool
--   (it might be good to have duplicates of the connectives also on Bool level)
fun	BooleanC : Class;
	BooleanCConforms2BooleanC : Subtype BooleanC BooleanC;
	true : Instance BooleanC; false : Instance BooleanC;
	orBool : Instance BooleanC -> Instance BooleanC -> Instance BooleanC;
	xorBool : Instance BooleanC -> Instance BooleanC -> Instance BooleanC;
	andBool : (p,q : Instance BooleanC) -> Instance BooleanC;
	notBool : Instance BooleanC -> Instance BooleanC;
	impliesBool : (p,q : Instance BooleanC) -> Instance BooleanC;
	-- no ifThenElseBool. 

--
-- Sent 
--
	sentEq : Sent -> Sent -> Sent;
	orS : Sent -> Sent -> Sent;
	xorS : Sent -> Sent -> Sent;
	andS : (p,q : Sent) -> Sent;
	notS : Sent -> Sent;
	impliesS : (p,q : Sent) -> Sent;
	ifThenElse : (c:Class) -> Sent -> Instance c -> Instance c -> Instance c;
	ifThenElseS : Sent -> Sent -> Sent -> Sent;
	    
    -- This is to allow lists of 'and' conjunctions to be constructed.
    -- and treated differently then cases where there is just a single 'and'.
    oneAnd : Sent -> Sent -> AndList;
	consAnd : Sent -> AndList -> AndList;
	posAndList2Sent : AndList -> Sent;
	negAndList2Sent : AndList -> Sent;
	
	oneOr : Sent -> Sent -> OrList;
	consOr :  Sent -> OrList -> OrList;
	posOrList2Sent : OrList -> Sent;
	negOrList2Sent : OrList -> Sent;


--
-- Integer
--
fun	IntegerC : Class;
	intAdd : Instance IntegerC -> Instance IntegerC -> Instance IntegerC;
	intSub : Instance IntegerC -> Instance IntegerC -> Instance IntegerC;
	intUnaryMinus : Instance IntegerC -> Instance IntegerC;
	intTimes : Instance IntegerC -> Instance IntegerC -> Instance IntegerC;
	intDiv2Real : Instance IntegerC -> Instance IntegerC -> Instance RealC;
	intAbs : Instance IntegerC -> Instance IntegerC;
	intDiv2Int : Instance IntegerC -> Instance IntegerC -> Instance IntegerC;
	intMod : Instance IntegerC -> Instance IntegerC -> Instance IntegerC;
	-- why are max and min defined for Integer too? daniels
	intMax : Instance IntegerC -> Instance IntegerC -> Instance IntegerC;
	intMin : Instance IntegerC -> Instance IntegerC -> Instance IntegerC;
	
	int : Int -> Instance IntegerC;
	IntegerCConforms2RealC : Subtype IntegerC RealC;
	IntegerCConforms2IntegerC : Subtype IntegerC IntegerC;

	oneSum : Instance IntegerC -> Instance IntegerC -> SumList;
	consSum : Instance IntegerC -> SumList -> SumList;
	sumList2Integer : SumList -> Instance IntegerC;
	
	oneProduct : Instance IntegerC -> Instance IntegerC -> ProductList;
	consProduct : Instance IntegerC -> ProductList -> ProductList;
	productList2Integer : ProductList -> Instance IntegerC;



--
-- Real
--
	
fun	RealC : Class;
	realAdd : (a,b : Instance RealC) -> Instance RealC;
	realSub : (a,b : Instance RealC) -> Instance RealC;
	realTimes : (a,b : Instance RealC) -> Instance RealC;
	realDiv : (a,b : Instance RealC) -> Instance RealC;
	realUnaryMinus : Instance RealC -> Instance RealC;
	realAbs : Instance RealC -> Instance RealC;
	realFloor : Instance RealC -> Instance IntegerC;
	realRound : Instance RealC -> Instance IntegerC;
	realMax : (a,b : Instance RealC) -> Instance RealC;
	realMin : (a,b : Instance RealC) -> Instance RealC;
	realLT : (a,b : Instance RealC) -> Sent;
	realGT : (a,b : Instance RealC) -> Sent;
	realLTE : (a,b : Instance RealC) -> Sent;
	realGTE : (a,b : Instance RealC) -> Sent;

	RealCConforms2RealC : Subtype RealC RealC;
	
--
-- Strings
--
	
fun	StringC : Class;
	StringCConforms2StringC : Subtype StringC StringC;
	stringLiteral : String -> Instance StringC;
	stringSize : Instance StringC -> Instance IntegerC;
	stringConcat : (a,b : Instance StringC) -> Instance StringC;
	stringToUpper : Instance StringC -> Instance StringC;
	stringToLower : Instance StringC -> Instance StringC;
	stringSubstring : Instance StringC -> (a,b : Instance IntegerC) -> Instance StringC;

--
-- Iterators
--
fun
	instIterSingle : (iter, e : Class) -> (Instance iter -> Instance e) -> InstIter iter e;
	instIterMany : (iter, e : Class) -> (Instance iter -> InstIter iter e) -> InstIter iter e;
	sentIterSingle : (iter : Class) -> (Instance iter -> Sent) -> SentIter iter;
	sentIterMany : (iter : Class) -> (Instance iter -> SentIter iter) -> SentIter iter;
--
-- Collection
--
fun	Collection : Class -> Class;
	size : (c:Class) -> (o : Instance (Collection c)) -> Instance IntegerC;
	includes : (c,d:Class) -> Instance (Collection c) -> Instance d ->  Sent; -- no use of OclAny
	excludes : (c,d:Class) -> Instance (Collection c) -> Instance d -> Sent;
	count : (c:Class) -> Instance (Collection c) -> Instance c -> Instance IntegerC;
	includesAll : (c:Class) -> (a,b : Instance (Collection c)) -> Sent;
	excludesAll : (c:Class) -> (a,b : Instance (Collection c)) -> Sent;
	isEmpty : (c:Class) -> Instance (Collection c) -> Sent;
	notEmpty : (c:Class) -> Instance (Collection c) -> Sent;
	sum : (c:Class) -> Instance (Collection c) -> Instance c; -- note diff from OCL

	exists : (c:Class) -> Instance (Collection c) -> SentIter c -> Sent;
	forAll : (c:Class) -> Instance (Collection c) -> SentIter c -> Sent;
	isUnique : (c,d : Class) -> Instance (Collection c) -> (InstIter c d) -> 
		Sent;
	sortedBy : (c,d : Class) -> Instance (Collection c) -> (InstIter c d) -> 
		Instance (Sequence c);  -- note diff OCL
	iterate : (c, a: Class) -> (o: Instance (Collection c)) ->
		(init : Instance a) -> (Instance c -> Instance a -> Instance a) -> Instance a;
	any : (c:Class) -> Instance (Collection c) -> SentIter c -> Instance c;
	one : (c:Class) -> Instance (Collection c) -> SentIter c -> Sent;
	collConforms : (sub,super:Class) -> Subtype sub super -> Subtype (Collection sub) (Collection super);

--
-- sets
--
	Set : Class -> Class;
	unionSS : (c:Class) -> Instance (Set c) -> Instance (Set c) -> Instance (Set c);
	unionSB : (c:Class) -> Instance (Set c) -> Instance (Bag c) -> Instance (Bag c);
	intersectionSS : (c:Class) -> (a,b : Instance (Set c)) -> Instance (Set c);
	intersectionSB : (c:Class) -> Instance (Set c) -> Instance (Bag c) -> Instance (Set c);
	subS : (c:Class) -> (a,b : Instance (Set c)) -> Instance (Set c);
	includingS : (c:Class) -> Instance (Set c) -> Instance c -> Instance (Set c);
	excludingS : (c:Class) -> Instance (Set c) -> Instance c -> Instance (Set c);
	symmetricDiff : (c:Class) -> (a,b : Instance (Set c)) -> Instance (Set c);
	selectSet : (c:Class) -> Instance (Set c) -> SentIter c -> Instance (Set c);
	rejectSet : (c:Class) -> Instance (Set c) -> SentIter c -> Instance (Set c);
	collectSet : (c,d:Class) -> Instance (Set c) -> InstIter c d -> Instance (Bag d);
	countSet : (c:Class) -> Instance (Set c) -> Instance c -> Instance IntegerC;
	setAsSequence : (c:Class) -> Instance (Set c) -> Instance (Sequence c);
	setAsBag : (c:Class) -> Instance (Set c) -> Instance (Bag c);
	setConforms2coll : (sub,super:Class) -> Subtype sub super -> Subtype (Set sub) (Collection super);
	setConforms : (sub,super:Class) -> Subtype sub super -> Subtype (Set sub) (Set super);

--	
-- bags
--
	Bag : Class -> Class;
	unionBB : (c:Class) -> (a,b : Instance (Bag c)) -> Instance (Bag c);
	unionBS : (c:Class) -> Instance (Bag c) -> Instance (Set c) -> Instance (Bag c);
	intersectionBB : (c:Class) -> (a,b : Instance (Bag c)) -> Instance (Bag c); 
	intersectionBS : (c:Class) -> Instance (Bag c) -> Instance (Set c) -> Instance (Set c);
	includingB : (c:Class) -> Instance (Bag c) -> Instance c -> Instance (Bag c);
	excludingB : (c:Class) -> Instance (Bag c) -> Instance c -> Instance (Bag c);
	selectBag : (c:Class) -> Instance (Bag c) -> SentIter c -> Instance (Bag c);
	rejectBag : (c:Class) -> Instance (Bag c) -> SentIter c -> Instance (Bag c);
	collectBag : (c,d:Class) -> Instance (Bag c) -> InstIter c d -> Instance (Bag d);
	countBag : (c:Class) -> Instance (Bag c) -> Instance c -> Instance IntegerC;
	bagAsSequence : (c:Class) -> Instance (Bag c) -> Instance (Sequence c);
	bagAsSet : (c:Class) -> Instance (Bag c) -> Instance (Set c);
	bagConforms2coll : (sub,super:Class) -> Subtype sub super -> Subtype (Bag sub) (Collection super);
	bagConforms : (sub,super:Class) -> Subtype sub super -> Subtype (Bag sub) (Bag super);

--
-- sequences	
--
	Sequence : Class -> Class;
	unionSeq : (c:Class) -> (a,b : Instance (Sequence c)) -> Instance (Sequence c);
	append : (c:Class) -> Instance (Sequence c) -> Instance c ->
		Instance (Sequence c);
	prepend : (c:Class) -> Instance (Sequence c) -> Instance c ->
		Instance (Sequence c);
	subSequence : (c:Class) -> Instance (Sequence c) -> 
		(a,b : Instance IntegerC) -> Instance (Sequence c);
	at : (c:Class) -> Instance (Sequence c) -> Instance IntegerC -> Instance c;
	first : (c:Class) -> (o : Instance (Sequence c)) -> Instance c;
	last : (c:Class) -> (o: Instance (Sequence c)) -> Instance c;
	includingSeq : (c:Class) -> Instance (Sequence c) -> Instance c -> Instance (Sequence c);
	excludingSeq : (c:Class) -> Instance (Sequence c) -> Instance c -> Instance (Sequence c);
	selectSeq : (c:Class) -> Instance (Sequence c) -> SentIter c  -> Instance (Sequence c);
	rejectSeq : (c:Class) -> Instance (Sequence c) -> SentIter c  -> Instance (Sequence c);
	collectSeq : (c,d : Class) -> Instance (Sequence c) -> InstIter c d -> Instance (Sequence d);
	-- no particular iterate for Sequences...
	seqAsBag : (c:Class) -> Instance (Sequence c) -> Instance (Bag c);
	seqAsSet : (c:Class) -> Instance (Sequence c) -> Instance (Set c);
	seqConforms2coll : (sub,super:Class) -> Subtype sub super -> Subtype (Sequence sub) (Collection super);
	seqConforms : (sub,super:Class) -> Subtype sub super -> Subtype (Sequence sub) (Sequence super);

    -- Collection literals
    emptySet : (c:Class) -> Instance (Set c);
    emptySeq : (c:Class) -> Instance (Sequence c);
    emptyBag : (c:Class) -> Instance (Bag c);
    
    singletonSet : (c:Class) -> Instance c -> Instance (Set c);
    singletonSeq : (c:Class) -> Instance c -> Instance (Sequence c);
    singletonBag : (c:Class) -> Instance c -> Instance (Bag c);
    
	twoColl : (c:Class) -> Instance c -> Instance c -> CollList c; 
	consColl : (c:Class) -> Instance c -> CollList c -> CollList c;
	listAsSeq : (c:Class) -> CollList c -> Instance (Sequence c);
	listAsSet : (c:Class) -> CollList c -> Instance (Set c);
	listAsBag : (c:Class) -> CollList c -> Instance (Bag c);
	-- diff. from OCL: we do not allow several "range expressions" in one literal
	rangeAsSeq : (from,to : Instance IntegerC) -> Instance (Sequence IntegerC);
	rangeAsSet : (from,to : Instance IntegerC) -> Instance (Set IntegerC);
	rangeAsBag : (from,to : Instance IntegerC) -> Instance (Bag IntegerC);



};
