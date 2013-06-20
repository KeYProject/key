// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



/* -*-antlr-*- */
header {
    package de.uka.ilkd.key.speclang.jml.translation;

    import java.io.StringReader;

    import de.uka.ilkd.key.collection.*;
    import de.uka.ilkd.key.java.JavaInfo;
    import de.uka.ilkd.key.java.Position;
    import de.uka.ilkd.key.java.Services;
    import de.uka.ilkd.key.java.abstraction.*;
    import de.uka.ilkd.key.java.expression.literal.StringLiteral;
    import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
    import de.uka.ilkd.key.ldt.*;
    import de.uka.ilkd.key.logic.*;
    import de.uka.ilkd.key.logic.op.*;
    import de.uka.ilkd.key.logic.sort.*;
    import de.uka.ilkd.key.parser.ParserException;
    import de.uka.ilkd.key.proof.OpReplacer;
    import de.uka.ilkd.key.speclang.PositionedString;
    import de.uka.ilkd.key.speclang.translation.*;
    import de.uka.ilkd.key.util.Pair;
    import de.uka.ilkd.key.util.Triple; 

    import java.math.BigInteger;
    import java.util.List;
    import java.util.Map;
    import java.util.LinkedHashMap;
}

class KeYJMLParser extends Parser;
options {
    importVocab=KeYJMLLexer;
    k = 2;
    defaultErrorHandler=false;
}

{
    private static final TermBuilder TB = TermBuilder.DF;

    private Services services;
    private JavaInfo javaInfo;
    private KeYJavaType containerType;
    private IntegerLDT intLDT;
    private HeapLDT heapLDT;
    private LocSetLDT locSetLDT;
    private BooleanLDT booleanLDT;
    private SLTranslationExceptionManager excManager;
    private List<PositionedString> warnings = new java.util.ArrayList<PositionedString>();

    private JMLTranslator translator;

    private ProgramVariable selfVar;
    private ImmutableList<ProgramVariable> paramVars;
    private ProgramVariable resultVar;
    private ProgramVariable excVar;
    private Map<LocationVariable,Term> atPres;
    
    // Helper objects
    private JMLResolverManager resolverManager;
    private JavaIntegerSemanticsHelper intHelper;

    
    public KeYJMLParser(TokenStream lexer,
		String fileName,
		Position offsetPos,
		Services services,
		KeYJavaType specInClass,
		ProgramVariable self,
		ImmutableList<ProgramVariable> paramVars,
		ProgramVariable result,
		ProgramVariable exc,
		Map<LocationVariable,Term> atPres) {
	this(lexer);

	// save parameters
	this.services       = services;
	this.javaInfo       = services.getJavaInfo();
	containerType  =   specInClass;
	this.intLDT         = services.getTypeConverter().getIntegerLDT();
	this.heapLDT        = services.getTypeConverter().getHeapLDT();
	this.locSetLDT      = services.getTypeConverter().getLocSetLDT();
	this.booleanLDT     = services.getTypeConverter().getBooleanLDT();
	this.excManager     = new SLTranslationExceptionManager(this,
				    				fileName, 
				    				offsetPos);
        this.translator     = new JMLTranslator(excManager, services);
	
	this.selfVar	    = self;
	this.paramVars      = paramVars;
	this.resultVar      = result;
	this.excVar	    = exc;
	this.atPres         = atPres;

        intHelper = new JavaIntegerSemanticsHelper(services, excManager);
	// initialize helper objects
	this.resolverManager = new JMLResolverManager(this.javaInfo,
						      specInClass,
						      selfVar,
						      this.excManager);

	// initialize namespaces
	resolverManager.pushLocalVariablesNamespace();
	if(paramVars != null) {
	    resolverManager.putIntoTopLocalVariablesNamespace(paramVars);
	}
	if(resultVar != null) {
	    resolverManager.putIntoTopLocalVariablesNamespace(resultVar);
	}
    }
    
    
    public KeYJMLParser(PositionedString ps,
		Services services,
		KeYJavaType specInClass,
		ProgramVariable self,
		ImmutableList<ProgramVariable> paramVars,
		ProgramVariable result,
		ProgramVariable exc,
		Map<LocationVariable,Term> atPres) {
	this(new KeYJMLLexer(new StringReader(ps.text)), 
	     ps.fileName, 
	     ps.pos,
	     services,
	     specInClass,
	     self,
	     paramVars,
	     result,
	     exc,
	     atPres);
    }


    public SLTranslationExceptionManager getExceptionManager() {
        return excManager;
    }


    private void raiseError(String msg) throws SLTranslationException {
	throw excManager.createException(msg);
    }    
    
    private void raiseError(String msg, Token t) throws SLTranslationException {
	throw excManager.createException(msg, t);
    }
    
    private void raiseError(String msg, Token t, Exception cause) throws SLTranslationException {
        throw excManager.createException(msg, t, cause);
    }
    
    private void raiseNotSupported(String feature) 
	    throws SLTranslationException {
	throw excManager.createWarningException(feature + " not supported"); 
    }
    
    /**
     * This is used for features without semantics such as labels or annotations.
     * @author bruns
     * @since 1.7.2178
     */
    private void addIgnoreWarning(String feature, Token t) {
        String msg = feature + " is not supported and has been silently ignored.";
        warnings.add(new PositionedString(msg,t));
    }
    
    public List<PositionedString> getWarnings(){
        // mutable -- but who cares?
        return warnings;
    }
	

    public Term parseExpression() throws SLTranslationException {
	Term result = null;

	try {
	    result = expression().getTerm();
	} catch (antlr.ANTLRException e) {
	    throw excManager.convertException(e);
	}

	return TB.convertToFormula(result, services);
    }


    public ImmutableList<ProgramVariable> parseVariableDeclaration() throws SLTranslationException {

	Pair<KeYJavaType,ImmutableList<LogicVariable>> vars;
	try {
	    vars = quantifiedvardecls();
	} catch (antlr.ANTLRException e) {
	    throw excManager.convertException(e);
	}

	ImmutableList<ProgramVariable> result = ImmutableSLList.<ProgramVariable>nil();
	for(LogicVariable lv : vars.second) {
	    ProgramVariable pv 
	    	= new LocationVariable(new ProgramElementName(
	    	                           lv.name().toString()), 
	                               vars.first);
	    result = result.append(pv);
	}
	return result;
    }



    /**
     * Extracts a term's subterms as an array.
     */
    private Term[] getSubTerms(Term term) {
	Term[] result = new Term[term.arity()];
	for(int i = 0; i < term.arity(); i++) {
	    result[i] = term.sub(i);
	    assert result[i] != null;
	}
	return result;
    }


    /**
     * Extracts the sorts from an array of terms as an array.
     */
    private Sort[] getSorts(Term[] terms) {
	Sort[] result = new Sort[terms.length];
	for(int i = 0; i < terms.length; i++) {
	    result[i] = terms[i].sort();
	}
	return result;
    }

	private LocationVariable getBaseHeap() {
		return services.getTypeConverter().getHeapLDT().getHeap();
	}

	private LocationVariable getSavedHeap() {
		return services.getTypeConverter().getHeapLDT().getSavedHeap();
	}

    /**
     * Converts a term so that all of its non-rigid operators refer to the pre-state.
     */
    // TODO: remove when all clients have been moved to JMLTranslator
    private Term convertToOld(final Term term) {
	    assert atPres != null && atPres.get(getBaseHeap()) != null;
	    Map<Term, Term> map = new LinkedHashMap<Term, Term>();
        for (LocationVariable heap : atPres.keySet()) {
            Term heapAtPre = atPres.get(heap);
            if (heapAtPre != null) {
                map.put(TB.var(heap), heapAtPre);
            }
        }
	    OpReplacer or = new OpReplacer(map);
	    return or.replace(term);
    }

    private Term convertToBackup(Term term) {
	assert atPres != null && atPres.get(getSavedHeap()) != null;
	Map map = new LinkedHashMap();
	map.put(TB.var(getBaseHeap()), TB.var(getSavedHeap()));
        if(atPres.get(getBaseHeap()) != null) {
	  map.put(atPres.get(getBaseHeap()), atPres.get(getSavedHeap()));
        }
	OpReplacer or = new OpReplacer(map);
	return or.replace(term);
    }


    private String createSignatureString(ImmutableList<SLExpression> signature) {
	if (signature == null || signature.isEmpty()) {
	    return "";
	}
	String sigString = "";
	
	for(SLExpression expr : signature) {
	    sigString += expr.getType().getFullName() + ", ";
	}
	
	return sigString.substring(0, sigString.length() - 2);
    }
    
    
    private SLExpression lookupIdentifier(String lookupName,
					  SLExpression receiver,
					  SLParameters params,
					  Token t)
				       throws SLTranslationException {

	// Identifier with suffix in parantheses? Probably a method call
	// parse in the parameter list and call again
	try {
	    if (LA(1) == LPAREN) {
	    	return receiver;
	    }
	} catch (TokenStreamException e) {
            raiseError("internal Error: no further Token in Stream");
	}

	SLExpression result = null;
	try {
	 result = resolverManager.resolve(receiver,
	   			      lookupName,
				      params);
	} catch(SLTranslationException exc) {
	   // no type name found maybe package?
	}
	
	if(result != null) {
	    return result;
	}
    
	// no identifier found, maybe it was just a package prefix.
	// but package prefixes don't have a receiver!
	// Let primarysuffix handle faulty method call.
	if (receiver != null && params == null) {
	    raiseError("Identifier " + lookupName + " not found: " + 
	               lookupName);
	}
	
	return null;
    }
}


top returns [Object result = null] throws  SLTranslationException
:
    (   result = accessibleclause
    |   result = assignableclause
    |   result = breaksclause
    |   result = continuesclause
    |   result = dependsclause
    |   result = declassifyclause
    |   result = ensuresclause
    |   result = representsclause
    |   result = requiresclause
    |   result = respectsclause
    |   result = returnsclause
    |   result = signalsclause
    |   result = signalsonlyclause
    |   result = termexpression
    )
    (SEMI)? EOF
    ;


accessibleclause returns [Term result = null] throws SLTranslationException
:
    acc:ACCESSIBLE result=storeRefUnion
        { result = translator.translate(acc.getText(), Term.class, result, services); }
    ;


assignableclause returns [Term result = null] throws SLTranslationException
:
    ass:ASSIGNABLE 
    ( result=storeRefUnion
        { result = translator.translate(ass.getText(), Term.class, result, services); }
    | LESS_THAN_NOTHING // deprecated
        { result = TB.strictlyNothing(); }
    | STRICTLY_NOTHING
        { result = TB.strictlyNothing(); }
    )
    ;


declassifyclause returns  [ImmutableList<Term> result = ImmutableSLList.<Term>nil()] throws SLTranslationException
{
    Term declass = null;
    Term frompart = null;
    Term topart = null;
    Term ifpart = null;
}
:
    del:DECLASSIFY declass = predicate
    (FROM frompart = storeRefUnion)?
    (TO topart = storeRefUnion)?
    (IF ifpart = predicate)?
    { result = translator.translate(del.getText(), ImmutableList.class, declass, frompart, topart, ifpart, services); }
    ;


dependsclause returns [Triple<ObserverFunction,Term,Term> result=null] throws SLTranslationException
{
    SLExpression lhs, mby = null;
    Term rhs;
}
:
    dep:DEPENDS lhs=expression
    COLON rhs=storeRefUnion
    (MEASURED_BY mby=expression)? SEMI
        { result = translator.translate(
                dep.getText(), Triple.class, lhs, rhs, mby, services); }
    ;


requiresclause returns [Term result = null] throws SLTranslationException
:
    req:REQUIRES result=termexpression
            { result = translator.translate(req.getText(), Term.class, result, services); }
    ;


ensuresclause returns [Term result = null] throws SLTranslationException
:
    ens:ENSURES result=termexpression
            { result = translator.translate(ens.getText(), Term.class, result, services); }
    ;


representsclause returns [Pair<ObserverFunction,Term> result=null] throws SLTranslationException
{
    SLExpression lhs, rhs;
    Term t = null;
}
:
    rep:REPRESENTS lhs=expression
    {
        // TODO: move code out of the parser!
        if(!lhs.isTerm()
            || !(lhs.getTerm().op() instanceof ObserverFunction)
            || lhs.getTerm().sub(0).op() != heapLDT.getHeap()) {
            raiseError("Represents clause with unexpected lhs: " + lhs);
        } else if(selfVar != null
                  && ((ObserverFunction)lhs.getTerm().op()).isStatic()) {
            raiseError("Represents clauses for static model fields must be static.");
        }
    }
    (
        { // TODO: move code out of the parser!
          !lhs.getTerm().sort().equals(locSetLDT.targetSort())}?
        (
            (LARROW | EQUAL_SINGLE) rhs=expression
            {   // TODO: move code out of the parser!
                if(!rhs.isTerm()) {
                    raiseError("Represents clause with unexpected rhs: " + rhs);
                }
                Term rhsTerm = rhs.getTerm();
                if(rhsTerm.sort() == Sort.FORMULA) {
                    rhsTerm = TB.ife(rhsTerm, TB.TRUE(services), TB.FALSE(services));
                }
                t = TB.equals(lhs.getTerm(), rhsTerm);
            }
        )
        |
        { // TODO: move code out of the parser!
          lhs.getTerm().sort().equals(locSetLDT.targetSort())}?
        (
            (LARROW | EQUAL_SINGLE) t=storeRefUnion
            {   // TODO: move code out of the parser!
                t = TB.equals(lhs.getTerm(), t);
            }
        )
        |
        (
            SUCH_THAT t=predicate
        )
    )
    { result = translator.translate(rep.getText(), Pair.class, lhs, t, services); }
    ;


respectsclause returns  [ImmutableList<Term> result = ImmutableSLList.<Term>nil()] throws SLTranslationException {
    Term term = null;
}
:
    resp:RESPECTS
    term = storeref { result = result.append(term); }
    (COMMA term = storeref { result = result.append(term); })*
        { result = translator.translate(resp.getText(), ImmutableList.class, result, services); }
    ;


signalsclause returns [Term result=null] throws SLTranslationException
{
    KeYJavaType excType = null;
    Term pred = null;
    String vName = null;
    LogicVariable eVar = null;
}
:
	sig:SIGNALS LPAREN excType=referencetype (id:IDENT { vName = id.getText(); })? RPAREN
	{
	    if (vName != null) {
		eVar = new LogicVariable(new Name(vName), excType.getSort());
		resolverManager.pushLocalVariablesNamespace();
		resolverManager.putIntoTopLocalVariablesNamespace(eVar, excType);
	    }
	}
	(result = predornot)?
	{
	    if (vName != null) {
		resolverManager.popLocalVariablesNamespace();
	    }
            result = translator.translate(sig.getText(), Term.class, result, eVar, excVar, excType, services);
	}
    ;


signalsonlyclause returns [Term result = null]
throws SLTranslationException {
    ImmutableList<KeYJavaType> typeList = ImmutableSLList.<KeYJavaType>nil();
    KeYJavaType type = null;
}
:
    sigo:SIGNALS_ONLY
    (   NOTHING
      | type = referencetype { typeList = typeList.append(type); }
        (COMMA type = referencetype { typeList = typeList.append(type); })*
    )
    { result = translator.translate(sigo.getText(), Term.class, typeList, this.excVar, services); }
    ;


termexpression returns [Term result = null] throws SLTranslationException {
    SLExpression exp = null;
}
:
    exp=expression { result = (Term) exp.getTerm(); }
    ;


breaksclause returns [Pair result=null] throws SLTranslationException
{
    String label = null;
    Term pred = null;
}
:
	breaks:BREAKS LPAREN (id:IDENT { label = id.getText(); })? RPAREN
	(pred = predornot)?
	{
        result = translator.translate(breaks.getText(), Pair.class, pred, label, services);
	}
;


continuesclause returns [Pair result=null] throws SLTranslationException
{
    String label = null;
    Term pred = null;
}
:
	continues:CONTINUES LPAREN (id:IDENT { label = id.getText(); })? RPAREN
	(pred = predornot)?
	{
        result = translator.translate(continues.getText(), Pair.class, pred, label, services);
	}
	;


returnsclause returns [Term result=null] throws SLTranslationException
{
    Term pred = null;
}
:
	rtrns:RETURNS
	(result = predornot)?
	{
        result = translator.translate(rtrns.getText(), Term.class, result, services);
	}
    ;	


storeRefUnion returns [Term result = null] throws SLTranslationException {
    ImmutableList<Term> list = null;
}
:   list = storeRefList
    { result = TB.union(services, list); };


storeRefList returns [ImmutableList<Term> result = ImmutableSLList.<Term>nil()]
        throws SLTranslationException {
    Term t = null;
}
:   t = storeref { result = result.append(t); }
	(COMMA t = storeref { result = result.append(t); } )*;



storeRefIntersect returns [Term result = null] throws SLTranslationException {
    ImmutableList<Term> list = null;
}
:   list = storeRefList { result = TB.intersect(services, list); };


storeref returns [Term result = null] throws SLTranslationException {
    SLExpression expr;
}
:       NOTHING { result = TB.empty(services); }
    |   EVERYTHING { result = TB.createdLocs(services); }
    |   NOT_SPECIFIED { result = TB.createdLocs(services); }
    |   result = storeRefExpr;


createLocset returns [Term result = null] throws SLTranslationException
{
    ImmutableList<SLExpression> list;
}
:
    (LOCSET | SINGLETON) LPAREN list=exprList RPAREN
    {
        result = translator.translate("create locset", Term.class, list, services);
    }
    ;


exprList returns [ImmutableList<SLExpression> result = ImmutableSLList.<SLExpression>nil()]
        throws SLTranslationException {
    SLExpression expr = null;
}
:   expr = expression { result = result.append(expr); }
	(COMMA expr = expression { result = result.append(expr); } )*;


storeRefExpr returns [Term result = null] throws SLTranslationException
{
    SLExpression expr;
}
:
    expr=expression 
    {
        result = translator.translate("store_ref_expr", Term.class, expr, services);
    }
    ;


specarrayrefexpr[SLExpression receiver, String fullyQualifiedName, Token lbrack] 
               returns [SLExpression result = null] 
               throws SLTranslationException
{
    SLExpression rangeFrom=null;
    SLExpression rangeTo=null;
}
:
    (
	( rangeFrom=expression (DOTDOT rangeTo=expression)? )
	| MULT
    )
    {
        result = translator.translate("array reference", SLExpression.class, services, receiver, fullyQualifiedName, lbrack, rangeFrom, rangeTo);
    }
;


predornot returns [Term result=null] throws SLTranslationException
:
	result=predicate
    |   NOT_SPECIFIED
    |   SAME
    ;
    
predicate returns [Term result=null] throws SLTranslationException
{
    SLExpression expr;
}
:
	expr=expression
	{
	    if(!expr.isTerm() && expr.getTerm().sort() == Sort.FORMULA) {
	        raiseError("Expected a formula: " + expr);
	    } 
	    result = expr.getTerm();
	}
    ;


expression returns [SLExpression result=null] throws SLTranslationException
:
	result=assignmentexpr
	{
	    if(!result.isTerm()) {
	        raiseError("Expected a term: " + result);
	    }
	}
    ;

assignmentexpr returns [SLExpression result=null] throws SLTranslationException
:
	result=conditionalexpr
    ;

	
conditionalexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression a,b;
}
:
	result=equivalenceexpr 
	(
	    QUESTIONMARK a=conditionalexpr COLON b=conditionalexpr
	    {
	    	result = translator.translate(JMLTranslator.JMLKeyWord.CONDITIONAL, services, result, a, b);
	    }
	)?
    ;


equivalenceexpr returns [SLExpression result=null] throws SLTranslationException {
    SLExpression right = null;
}
:
	result = impliesexpr
        (   eq:EQV_ANTIV right=equivalenceexpr
            { result = translator.translate(eq.getText(), SLExpression.class, result, right, services); }
        )?
    ;


	
impliesexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression expr;
}
:
	result=logicalorexpr 
	(
	    IMPLIES expr=impliesnonbackwardexpr
	    {
		result = new SLExpression(TB.imp(TB.convertToFormula(result.getTerm(), services),
		                                 TB.convertToFormula(expr.getTerm(), services)));
	    }
	    
	  |
	    (
		IMPLIESBACKWARD expr=logicalorexpr
		{
		    result = new SLExpression(TB.imp(TB.convertToFormula(expr.getTerm(), services),
		                                     TB.convertToFormula(result.getTerm(), services)));
		}
	    )+
	)?
;

impliesnonbackwardexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression expr;
}
:
	result=logicalorexpr
	(
	    IMPLIES expr=impliesnonbackwardexpr
	    {
		result = new SLExpression(TB.imp(TB.convertToFormula(result.getTerm(), services),
		                                 TB.convertToFormula(expr.getTerm(), services)));
	    }
	)?
;	

logicalorexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression expr;
}
:
	result=logicalandexpr
	(
	    LOGICALOR expr=logicalorexpr
	    {
		result = new SLExpression(TB.or(TB.convertToFormula(result.getTerm(), services),
		                                TB.convertToFormula(expr.getTerm(), services)));
	    }
	)?
;

logicalandexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression expr;
}
:
	result=inclusiveorexpr
	(
	    LOGICALAND expr=logicalandexpr
	    {
		result = new SLExpression(TB.and(TB.convertToFormula(result.getTerm(), services),
		                                 TB.convertToFormula(expr.getTerm(), services)));
	    }
	)?
;


inclusiveorexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression expr;
}
:
	result=exclusiveorexpr 
	(
	    INCLUSIVEOR expr=inclusiveorexpr
	    {
	       if(intHelper.isIntegerTerm(result)) {
                   result = intHelper.buildPromotedOrExpression(result,expr);
               } else {
                   result = new SLExpression(TB.or(TB.convertToFormula(result.getTerm(), services),
                                                   TB.convertToFormula(expr.getTerm(), services)));
               }
	    }
	)?
;


exclusiveorexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression expr;
}
:
	result=andexpr 
	(
	    XOR expr=exclusiveorexpr
	    {
	       if(intHelper.isIntegerTerm(result)) {
                   result = intHelper.buildPromotedXorExpression(result,expr);
               } else {
                   Term resultFormula = TB.convertToFormula(result.getTerm(), services);
                   Term exprFormula = TB.convertToFormula(expr.getTerm(), services);
                   result = new SLExpression(TB.or(TB.and(resultFormula, TB.not(exprFormula)), 
                                                   TB.and(TB.not(resultFormula), exprFormula)));
               }
	    }
	)?
;


andexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression expr;
}
:
	result=equalityexpr
	{
	    if(!result.isTerm()) {
		raiseError("Found a type where only a term is allowed: " 
			   + result);
	    }
	}
	(
	    AND expr=andexpr
	    { 
	       if(intHelper.isIntegerTerm(result)) {
                   result = intHelper.buildPromotedAndExpression(result, expr);
               } else {
                   result = new SLExpression(TB.and(TB.convertToFormula(result.getTerm(), services),
                                                    TB.convertToFormula(expr.getTerm(), services)));
               }
	    }
	)?
;

equalityexpr returns [SLExpression result=null] throws SLTranslationException
{
	SLExpression right = null;
}
	 :
	result=relationalexpr 
	(   eq:EQ_NEQ right=equalityexpr
	        { result = translator.translate(eq.getText(), SLExpression.class, result, right, services); }
	)?
;

//equalityexpr returns [SLExpression result=null] throws SLTranslationException
//{
//    Deque<Pair<Token,SLExpression>> right = null;
//}
//:
//    result = relationalexpr
//    right = equalityexprright
//    { 
//        assert right != null;
//        for (Pair<Token,SLExpression> pair: right) { 
//            result = translator.translate(pair.first.getText(), SLExpression.class, result, pair.second, services);
//        }
//    }
//;
///** Helper method to make equality expressions left associative. */
//equalityexprright returns [Deque<Pair<Token,SLExpression>> result= null] throws SLTranslationException
//{
//    SLExpression tmp = null;
//}
//:
//    (EQ | NEQ) =>
//        eq:EQ_NEQ
//        tmp = relationalexpr
//        result = equalityexprright
//    {
//        result.push(new Pair<Token,SLExpression>(eq,tmp));
//    }
//    |
//    EMPTY
//    {
//        result = new ArrayDeque<Pair<Token,SLExpression>>();
//    }
//;

relationalexpr returns [SLExpression result=null] throws SLTranslationException
{
    Function f = null;
    KeYJavaType type = null;
    SLExpression right = null;
    Token opToken = null;
}
:
	result=shiftexpr
	(
	    lt:LT right=shiftexpr 
	    {
		f = intLDT.getLessThan();
		opToken = lt;
	    }
	|
	    gt:GT right=shiftexpr
	    {
		f = intLDT.getGreaterThan();
		opToken = gt;
	    }
	|
	    leq:LEQ right=shiftexpr
	    {
		f = intLDT.getLessOrEquals();
		opToken = leq;
	    }
	|
	    geq:GEQ right=shiftexpr
	    {
		f = intLDT.getGreaterOrEquals();
		opToken = geq;
	    }
	|
	    io:INSTANCEOF type=typespec 
	    {
		f = type.getSort().getInstanceofSymbol(services);
		opToken = io;
	    }
	|
	    st:ST right=shiftexpr
	    {
		if (result.isTerm() || right.isTerm()) {
		    raiseError("Cannot build subtype expression from terms.", st);
		}
		assert result.isType();
		assert right.isType();
		
		if (result.getTerm() == null) {
		    raiseError("subtype expression <: only supported for" +
			" \\typeof() arguments on the left side.", st);
		}
		
		Sort os = right.getType().getSort();
		Function ioFunc = os.getInstanceofSymbol(services);
		
		result = new SLExpression(
		    TB.equals(
			TB.func(ioFunc, result.getTerm()),
			TB.TRUE(services)));
	    }
	)?
	{
	    if (f != null) {
		assert opToken != null;
		if (result.isType()) {
		    raiseError("Cannot build relational expression from type " +
			result.getType().getName() + ".", opToken);
		}
		assert result.isTerm();
		
		try {
			if (right == null) {
			    // instanceof-expression
			    result = new SLExpression(
				TB.and(TB.not(TB.equals(result.getTerm(), TB.NULL(services))),
				       TB.equals(TB.func(f, result.getTerm()), TB.TRUE(services))));
			} else {
			    if (right.isType()) {
			    raiseError("Cannot build relational expression from type " +
				right.getType().getName() + ".", opToken);
			    }
			    assert right.isTerm();
			    
			    result = new SLExpression(
				TB.func(f,result.getTerm(),right.getTerm()));
			}
		} catch (TermCreationException e) {
		    raiseError("Error in relational expression: " + e.getMessage());
		} catch (IllegalArgumentException e) {
		    raiseError("Internal error.");
		}
	    }
	}
;

shiftexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression e;
}
:
    result=additiveexpr
    (
	sr:SHIFTRIGHT e=additiveexpr
	{
        result = translator.<SLExpression>translate(sr.getText(), SLExpression.class, services, result, e);
	}
    |   
	sl:SHIFTLEFT e=additiveexpr 
	{
        result = translator.<SLExpression>translate(sl.getText(), SLExpression.class, services, result, e);
	}
    |   
	usr:UNSIGNEDSHIFTRIGHT e=additiveexpr 
	{
        result = translator.<SLExpression>translate(usr.getText(), SLExpression.class, services, result, e);
	}
    )*
; 


additiveexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression e;
}
:
    result=multexpr
    (
	plus:PLUS e=multexpr
	{
        result = translator.<SLExpression>translate(plus.getText(), SLExpression.class, services, result, e);
	}
    |
	minus:MINUS e=multexpr
	{
	    result = translator.<SLExpression>translate(minus.getText(), SLExpression.class, services, result, e);
	}
    )*
;


multexpr returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression e;
}
:
    result=unaryexpr
    (
	MULT e=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build multiplicative expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot multiply by type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();
	
	    result = intHelper.buildMulExpression(result, e);
	}
    |
	DIV e=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build multiplicative expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot divide by type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();

	    result = intHelper.buildDivExpression(result, e);
	}
    |
	MOD e=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build multiplicative expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot build modulo expression from type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();

	    result = intHelper.buildModExpression(result, e);
	}
    )*
;


unaryexpr returns [SLExpression result=null] throws SLTranslationException
:
    PLUS result=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build  +" + result.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    
	    result = intHelper.buildPromotedUnaryPlusExpression(result);
	}
    |
	MINUS result=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build  -" + result.getType().getName() + ".");
	    }
	    assert result.isTerm();

	    result = intHelper.buildUnaryMinusExpression(result);
	}
    |
	(LPAREN typespec RPAREN ) => result = castexpr
    |
	    result=unaryexprnotplusminus
;

castexpr returns  [SLExpression result = null] throws SLTranslationException
{
    KeYJavaType type = null;
}
:
LPAREN type=typespec RPAREN result=unaryexpr
{
    result = translator.translate(JMLTranslator.JMLKeyWord.CAST, services, intHelper, type, result);
}
;

unaryexprnotplusminus returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression e;
}
:
	NOT e=unaryexpr
	{
	    if (e.isType()) {
		raiseError("Cannot negate type " + e.getType().getName() + ".");
	    }
	    
	    Term t = e.getTerm();
	    assert t != null;
	    
	    if (t.sort() == Sort.FORMULA) {
		result = new SLExpression(TB.not(t));
	    } else if(t.sort() == booleanLDT.targetSort()) {
		result = new SLExpression(TB.not(TB.equals(t, TB.TRUE(services))));
	    } else {
		raiseError("Wrong type in not-expression: " + t);
	    }
	}
    |   
	BITWISENOT e=unaryexpr
	{
	    if(e.isType()) {
		raiseError("Cannot negate type " + e.getType().getName() + ".");
	    }
		
	    result = intHelper.buildPromotedNegExpression(e);
	}
	
    |
	result=postfixexpr
;


postfixexpr returns [SLExpression result=null] throws SLTranslationException
{
    String fullyQualifiedName = "";
    SLExpression expr = null;
}
:
	expr=primaryexpr
	{
	    fullyQualifiedName = LT(0).getText();
	}
	(
	    {
	        if (expr != null && expr.getType() == null) {
	            raiseError("SLExpression without a type: " + expr);
	        }/* else if (expr != null && expr.getType().getJavaType() instanceof PrimitiveType) {
		    raiseError("Cannot build postfix expression from primitive type.");
		}*/	    		
	    }
	    expr=primarysuffix[expr, fullyQualifiedName]
	    {	    
		fullyQualifiedName += "." + LT(0).getText();
	    }
	)*
	
	{
	    if (expr == null) {
		raiseError("Expression " + fullyQualifiedName + " cannot be resolved.");
	    }
	    result = expr; //.getTerm();
	}
	    
;

primaryexpr returns [SLExpression result=null] throws SLTranslationException
{
    Term s1, s2;
}
:
	result=constant
    |   id:IDENT     { result = lookupIdentifier(id.getText(), null, null, id); }
    |   inv:INV      { result = translator.translate(inv.getText(),services,
                                selfVar==null? null: TB.var(selfVar),containerType);}
    |   TRUE         { result = new SLExpression(TB.tt()); }
    |   FALSE        { result = new SLExpression(TB.ff()); }
    |   NULL         { result = new SLExpression(TB.NULL(services)); }
    |   result=jmlprimary 
    |   THIS       
        { 
            if(selfVar == null) {
            	raiseError("Cannot access \"this\" in a static context!"); 
            }
            result = new SLExpression(TB.var(selfVar), selfVar.getKeYJavaType());
        }
    |   new_expr
    |   array_initializer
;   

transactionUpdated
  returns [SLExpression result=null]
  throws SLTranslationException
{
   SLExpression expr;
   String fieldName = "<transactionConditionallyUpdated>";
}
:

   tk:TRANSACTIONUPDATED LPAREN expr=expression RPAREN
   {
      result = lookupIdentifier(fieldName, expr, null, tk);
   }
;

primarysuffix[SLExpression receiver, String fullyQualifiedName] 
		returns [SLExpression result=null] 
		throws SLTranslationException
{
    String lookupName = null;   
    ImmutableList<SLExpression> params = ImmutableSLList.<SLExpression>nil();
}
:
{
    lookupName = fullyQualifiedName;
}
(
	DOT id:IDENT
	{
	    if(receiver == null) {
		// Receiver was only a package/classname prefix
		lookupName = fullyQualifiedName + "." + id.getText();
	    } else {
		lookupName = id.getText();
	    }
	    try {
	    	result = lookupIdentifier(lookupName, receiver, null, id);
	    } catch(SLTranslationException e) {
	    	result = lookupIdentifier(fullyQualifiedName + "." + lookupName, null, null, id);
	    }
	}
    |
    DOT THIS
    {
    	result = new SLExpression(
    		services.getTypeConverter().findThisForSort(receiver.getType().getSort(),
    							    TB.var(selfVar), 
    							    javaInfo.getKeYJavaType(selfVar.sort()), 
    							    true),
                receiver.getType());
    }
    |
    DOT INV
    {
        result = translator.translate("\\inv",services,receiver.getTerm(),receiver.getType());
    }
    |	{
    	    if(receiver != null) {
		lookupName = LT(0).getText();
	    }
	}
	l:LPAREN (params=expressionlist)? RPAREN
	{
	    result = lookupIdentifier(lookupName, receiver, new SLParameters(params), l);
	    if (result == null) {
		raiseError("Method " + lookupName + "("
		           + createSignatureString(params) + ") not found!", l);
	    }
	}
    |
	lbrack:LBRACKET result=specarrayrefexpr[receiver, fullyQualifiedName, lbrack] RBRACKET
    |    
         DOT MULT
         {
	     result = new SLExpression(TB.allFields(services, receiver.getTerm()),
	                               javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
         }
	
)	
;

new_expr throws SLTranslationException
{
    KeYJavaType typ = null;
    ImmutableList<SLExpression> params;
}
:
	NEW typ=type ( 
	    LPAREN ( params=expressionlist )? RPAREN
	   |
	    array_dimensions (array_initializer)?
	   )
        {	
        	raiseNotSupported("'new' within specifications"); 
        }
    ;
    
array_dimensions throws SLTranslationException
:
    array_dimension
    // TODO handle higher dimensions
;
    
array_dimension throws SLTranslationException
{
    SLExpression length;
}
:
    LBRACKET (length=expression)? RBRACKET
;
    
array_initializer throws SLTranslationException
{
    ImmutableList<SLExpression> init;
}
:
    LBRACE init=expressionlist RBRACE
    {
        raiseNotSupported("array initializer");
    }
;

expressionlist returns [ImmutableList<SLExpression> result=ImmutableSLList.<SLExpression>nil()] 
               throws SLTranslationException
{ 
    SLExpression expr;
}
:
	expr=expression { result = result.append(expr); } (COMMA expr=expression {result = result.append(expr);} )* 
;

constant returns [SLExpression result=null] throws SLTranslationException
:
	result=javaliteral
;

javaliteral returns [SLExpression result=null] throws SLTranslationException
:
	result=integerliteral
    |
	l:STRING_LITERAL 
	{
	    Term charListTerm
	       = services.getTypeConverter()
	                 .convertToLogicElement(
	                 	new StringLiteral("\"" + l.getText() + "\""));
	    Function strPool 
	    	= (Function) services.getNamespaces()
	    	                     .functions()
	    	                     .lookup(CharListLDT.STRINGPOOL_NAME);
	    if(strPool == null) {
	        raiseError("string literals used in specification, "
	                   + "but string pool function not found");
	    }
	    Term stringTerm = TB.func(strPool, charListTerm);
	    return new SLExpression(stringTerm, 
	                            javaInfo.getKeYJavaType("java.lang.String"));
	}
    |
	CHAR_LITERAL 
	{
	    raiseNotSupported("character literals");
	}
    ;

integerliteral returns [SLExpression result=null] throws SLTranslationException
:
	result=decimalintegerliteral
    |
	result=hexintegerliteral
;

hexintegerliteral returns [SLExpression result=null] throws SLTranslationException
:
    n:HEXNUMERAL
    {
	BigInteger decInteger = new BigInteger(n.getText(), 16);
	result = new SLExpression(TB.zTerm(services, decInteger.toString()),
	                          javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT));
    }
;

decimalintegerliteral returns [SLExpression result=null] throws SLTranslationException
:
	result=decimalnumeral
;

decimalnumeral returns [SLExpression result=null] throws SLTranslationException
:
    n:DIGITS
    {
	result = new SLExpression(TB.zTerm(services,n.getText()),
	                          javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT));
    }
;

jmlprimary returns [SLExpression result=null] throws SLTranslationException
{
    ImmutableList<SLExpression> list = null;
    ImmutableList<Term> tlist = null;
    SLExpression e1 = null;
    SLExpression e2 = null;
    SLExpression e3 = null;
    KeYJavaType typ;
    Term t, t2 = null;
    Token tk = null;
    Pair<KeYJavaType,ImmutableList<LogicVariable>> declVars = null;    
}
:
	RESULT
	{
	    if(resultVar==null) {
		raiseError("\\result used in wrong context");
	    } else
	    result = new SLExpression(TB.var(resultVar), resultVar.getKeYJavaType());
	}
    |
	(LPAREN QUANTIFIER) => t=specquantifiedexpression { result = new SLExpression(t); }
    |
        (LPAREN BSUM) => result=bsumterm
    |
        (LPAREN SEQDEF) => result=seqdefterm
    |
	(OLD | PRE) => result=oldexpression
	
    |   result = transactionUpdated
    |
	BACKUP LPAREN result=expression RPAREN
	{
	    if (atPres == null || atPres.get(getSavedHeap()) == null) {
		raiseError("JML construct " +
			   "\\backup not allowed in this context.");
	    }	    
	    typ = result.getType();
	    if(typ != null) {
	      result = new SLExpression(convertToBackup(result.getTerm()), 
	                                result.getType());
	    } else {
	      result = new SLExpression(convertToBackup(result.getTerm()));
	    }
	}
    |   
	CREATED LPAREN result=expression RPAREN
	{
		raiseNotSupported("\\created is deliberately not supported in this KeY version, you should not need it");
	}
    |
	NONNULLELEMENTS LPAREN result=expression RPAREN
	{
	    t = result.getTerm();
	    Term resTerm = TB.not(TB.equals(t, TB.NULL(services)));

	    if (t.sort() instanceof ArraySort) {
		LogicVariable i = new LogicVariable(new Name("i"), javaInfo
				.getKeYJavaType(PrimitiveType.JAVA_INT)
				.getSort());

		// See JML reference manual
		// http://www.cs.iastate.edu/~leavens/JML/jmlrefman/jmlrefman_11.html#SEC139		
		Term range = TB.and(
		    TB.leq(TB.zero(services), TB.var(i), services),
		    TB.lt(TB.var(i), TB.dotLength(services, t), services));
		Term body = TB.equals(
		    TB.dotArr(services, t, TB.var(i)),
		    TB.NULL(services));
		body = TB.not(body);
		body = TB.imp(range, body);

		result = new SLExpression(TB.and(resTerm, TB.all(i, body)));
	    } else {
	        raiseError("\\nonnullelements may only be applied to arrays");
	    }
	}
	
    |   desc:INFORMAL_DESCRIPTION 
	{
	    // was: raiseNotSupported("informal predicates");
	    result = translator.translate("(* *)", SLExpression.class, services, desc, 
	        selfVar, resultVar, paramVars, atPres == null ? null : atPres.get(getBaseHeap()));
	}
	
    |   escape:DL_ESCAPE LPAREN ( list=expressionlist )? RPAREN
        {
            result = translator.translate("\\dl_", SLExpression.class, escape, list, services);
        }
        
    |   NOT_MODIFIED LPAREN t=storeRefUnion RPAREN
        {
        result = new SLExpression(translator.translate("\\not_modified", Term.class, services, atPres == null ? null : atPres.get(getBaseHeap()), t));
        } 
	
    |   FRESH LPAREN list=expressionlist RPAREN
	{
	    if(atPres == null || atPres.get(getBaseHeap()) == null) {
	        raiseError("\\fresh not allowed in this context");
	    }
	    t = TB.tt();
	    final Sort objectSort = services.getJavaInfo().objectSort();
	    for(SLExpression expr: list) {
	        if(!expr.isTerm()) {
	            raiseError("Expected a term, but found: " + expr);
	        } else if(expr.getTerm().sort().extendsTrans(objectSort)) {
	            t = TB.and(t, 
	                       TB.equals(TB.select(services,
	                                           booleanLDT.targetSort(),
	                                           atPres.get(getBaseHeap()),
	                                           expr.getTerm(),
	                                           TB.func(heapLDT.getCreated())),
	                                 TB.FALSE(services)));
	        } else if(expr.getTerm().sort().extendsTrans(locSetLDT.targetSort())) {
	            t = TB.and(t, TB.subset(services, 
	                                    expr.getTerm(), 
	                                    TB.freshLocs(services, atPres.get(getBaseHeap()))));
	        } else {
	            raiseError("Wrong type: " + expr);
	        }
	    }
	    result = new SLExpression(t);
	} 

    |   REACH LPAREN t=storeref COMMA e1=expression COMMA e2=expression (COMMA e3=expression)? RPAREN
	{
        result = translator.translate("reach", SLExpression.class, t, e1, e2, e3, services);
	} 
	
    |   REACHLOCS LPAREN t=storeref COMMA e1=expression (COMMA e3=expression)? RPAREN
	{
        result = translator.translate("reachLocs", SLExpression.class, t, e1, e3, services);
	} 	
	
    |   DURATION LPAREN result=expression RPAREN 
	{
	    raiseNotSupported("\\duration");
	} 
	
    |   SPACE LPAREN result=expression RPAREN
	{
	    raiseNotSupported("\\space");
	} 
	
    |   WORKINGSPACE LPAREN result=expression RPAREN
	{
	    raiseNotSupported("\\working_space");
	} 
	
    |   TYPEOF LPAREN result=expression RPAREN
	{
	    result = new SLExpression(result.getTerm(),
	                              result.getType(),
	                              false);
	} 
	
    |   ELEMTYPE LPAREN result=expression RPAREN 
	{
	    raiseNotSupported("\\elemtype");
	} 
	
    |   TYPE_SMALL LPAREN typ=typespec RPAREN 
	{
	    result = new SLExpression(typ);
	} 
	
    |   LOCKSET
	{
	    raiseNotSupported("\\lockset");
	} 
	
    |   IS_INITIALIZED LPAREN typ=referencetype RPAREN 
	{
	    Term resTerm = TB.equals(
		TB.var(
		    javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, 
					  typ)),
		TB.TRUE(services));
	    result = new SLExpression(resTerm);
	} 
	
    |   INVARIANT_FOR LPAREN result=expression RPAREN 
	{
	    result = translator.translate("\\invariant_for", SLExpression.class, services, result);
	    
	} 
	
    |   ( LPAREN LBLNEG ) => LPAREN lblneg:LBLNEG IDENT result=expression RPAREN
	{
	    addIgnoreWarning("\\lblneg",lblneg);
	} 
	
    |   ( LPAREN LBLPOS ) => LPAREN lblpos:LBLPOS IDENT result=expression RPAREN 
	{
	    addIgnoreWarning("\\lblpos",lblpos);
	} 
	|   INDEX { result = translator.translate(JMLTranslator.JMLKeyWord.INDEX, services); }
	|   VALUES { result = translator.translate(JMLTranslator.JMLKeyWord.VALUES, services); }
    |   STRING_EQUAL LPAREN e1=expression COMMA e2=expression RPAREN
        {
	    Function strContent
	    	= (Function) services.getNamespaces()
            	                     .functions()
            	                     .lookup(CharListLDT.STRINGCONTENT_NAME);
            if(strContent == null) {
                raiseError("strings used in spec, but string content "
                           + "function not found");
            }
            return new SLExpression(TB.equals(TB.func(strContent, e1.getTerm()), 
                                              TB.func(strContent, e2.getTerm())));
        }

    |   EMPTYSET
        {
            result = translator.translate(JMLTranslator.JMLKeyWord.EMPTY, services, javaInfo);
        }

    |   t = createLocset
        { result = new SLExpression(t, javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET)); }
        
    |   (UNION | UNION_2) LPAREN t=storeRefUnion RPAREN
        { result = translator.translate(JMLTranslator.JMLKeyWord.UNION, t, javaInfo); }
        
    |   INTERSECT LPAREN t=storeRefIntersect RPAREN
        { result = translator.translate(JMLTranslator.JMLKeyWord.INTERSECT, t, javaInfo); }

    |   SETMINUS LPAREN t=storeref COMMA t2=storeref RPAREN
        {
            result = new SLExpression(TB.setMinus(services, t, t2),
                                      javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
        } 
        
    |   ALLFIELDS LPAREN e1=expression RPAREN
        {
            if(!e1.isTerm() || !e1.getTerm().sort().extendsTrans(services.getJavaInfo().objectSort())) {
                raiseError("Invalid argument to \\allFields: " + e1);
            }
            result = new SLExpression(TB.allFields(services, e1.getTerm()),
                                      javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
        }        
        
    |  ALLOBJECTS LPAREN t=storeref RPAREN
        {          
            result = new SLExpression(TB.allObjects(services, t.sub(1)),
                                      javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
        }                
    |   UNIONINF
        LPAREN 
        declVars=quantifiedvardecls
        SEMI
        {
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);
        }
        ((predicate SEMI) => t2=predicate SEMI | SEMI )? 
        t=storeref 
        RPAREN
        {
               resolverManager.popLocalVariablesNamespace();
               if(t2 == null) {
                  // unguarded version
	          result = new SLExpression(TB.infiniteUnion(services,
                                                       declVars.second.toArray(new QuantifiableVariable[declVars.second.size()]),
                                                       t),
                                      javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
               } else {
                  // guarded version
                  result = new SLExpression(TB.guardedInfiniteUnion(services,
                                                       declVars.second.toArray(new QuantifiableVariable[declVars.second.size()]),
                                                       t2, t),
                                      javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
               }
        }

    |   pd:DISJOINT LPAREN tlist=storeRefList RPAREN {
            result = translator.translate(pd.getText(), SLExpression.class, tlist, services);
        }

    |   SUBSET LPAREN t=storeref COMMA t2=storeref RPAREN
        {
            result = new SLExpression(TB.subset(services, t, t2));
        } 
        
    |   NEWELEMSFRESH LPAREN t=storeref RPAREN
        {
            result = new SLExpression(TB.subset(services, 
                                                t, 
                                                TB.union(services,
                                                         convertToOld(t),
                                                         TB.freshLocs(services, 
                                                         	      atPres == null ? null : atPres.get(getBaseHeap())))));
                                                        
        }
        
    |   SEQEMPTY
        {
            result = new SLExpression(TB.seqEmpty(services));
        }
    
    |   SEQSINGLETON LPAREN e1=expression RPAREN
        {
            result = new SLExpression(TB.seqSingleton(services, e1.getTerm()));
        }    
    
    |   SEQSUB LPAREN e1=expression COMMA e2=expression COMMA e3=expression RPAREN
        {
            result = new SLExpression(TB.seqSub(services, e1.getTerm(), e2.getTerm(), e3.getTerm()));
        }
        
    |   SEQREVERSE LPAREN e1=expression RPAREN
        {
            result = new SLExpression(TB.seqReverse(services, e1.getTerm()));
        } 
    |   SEQREPLACE LPAREN e1=expression COMMA e2=expression COMMA e3=expression RPAREN
        {
            // short for "e1[0..e2-1]+e3+e1[e2+1..e1.length-1]"
            final Term minusOne = TB.zTerm(services, "-1");
            final Term ante = TB.seqSub(services, e1.getTerm(), TB.zero(services), TB.add(services, e2.getTerm(), minusOne));
            final Term insert = TB.seqSingleton(services, e3.getTerm());
            final Term post = TB.seqSub(services, e1.getTerm(), TB.add(services, e2.getTerm(), TB.one(services)), TB.add(services, TB.seqLen(services, e1.getTerm()), minusOne));
            final Term put = TB.seqConcat(services, ante, TB.seqConcat(services, insert, post));
            result = new SLExpression(put);
        }
    |   (tk2: SEQCONCAT{tk=tk2;} | tk3: SEQGET{tk=tk3;} | tk4: INDEXOF{tk=tk4;})
        LPAREN e1=expression COMMA e2=expression RPAREN
        {
            result = translator.translate(tk.getText(), SLExpression.class, services, e1, e2);
        }
    |   LPAREN result=expression RPAREN
;

specquantifiedexpression returns [Term result = null] throws SLTranslationException
{
    SLExpression expr;
    Term p = TB.tt();
    boolean nullable = false;
    Pair<KeYJavaType,ImmutableList<LogicVariable>> declVars = null;
}
:
	LPAREN
	q:QUANTIFIER 
	(nullable=boundvarmodifiers)? 
	declVars=quantifiedvardecls SEMI
	{
	    resolverManager.pushLocalVariablesNamespace();
	    resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);
	} 
	((predicate SEMI) => p=predicate SEMI | SEMI)? 
	expr=expression
	{
	    resolverManager.popLocalVariablesNamespace();
	    
	    p = TB.convertToFormula(p, services);
	    result = translator.translate(q.getText(), Term.class, p, expr.getTerm(), declVars.first, declVars.second, nullable, services);
	}
	RPAREN
;
	
oldexpression returns [SLExpression result=null] throws SLTranslationException
{ KeYJavaType typ; }
:
    (
    PRE LPAREN result=expression RPAREN
    |
    OLD LPAREN result=expression (COMMA id:IDENT)? RPAREN
    )
    {
        if (atPres == null || atPres.get(getBaseHeap()) == null) {
        raiseError("JML construct " +
               "\\old not allowed in this context.");
        }
        
        if (id != null) addIgnoreWarning("\\old with label",id);
        
        typ = result.getType();
        if(typ != null) {
          result = new SLExpression(convertToOld(result.getTerm()), 
                                    result.getType());
        } else {
          result = new SLExpression(convertToOld(result.getTerm()));
        }
    }
;

bsumterm returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression a = null;
    SLExpression b = null;
    SLExpression t = null;
    Pair<KeYJavaType,ImmutableList<LogicVariable>> decls = null;
}:
        LPAREN
        q:BSUM decls=quantifiedvardecls 
        {	    
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(decls.second, decls.first);
        } 
        SEMI
        (
            a=expression SEMI  b=expression SEMI t=expression
        )
        {
            result = translator.translate(q.getText(), SLExpression.class, a, b, t, decls.first, decls.second, services);
            resolverManager.popLocalVariablesNamespace();
        }
        RPAREN
; exception
        catch [SLTranslationException ex] {
        resolverManager.popLocalVariablesNamespace();
        throw ex;
        }   


seqdefterm returns [SLExpression result=null] throws SLTranslationException
{
    SLExpression a = null;
    SLExpression b = null;
    SLExpression t = null;
    Pair<KeYJavaType,ImmutableList<LogicVariable>> decls = null;
}:
        LPAREN
        q:SEQDEF decls=quantifiedvardecls 
        {	    
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(decls.second, decls.first);
        } 
        SEMI
        (
            a=expression SEMI  b=expression SEMI t=expression
        )
        {
            result = translator.translate(q.getText(), SLExpression.class, a, b, t, decls.first, decls.second, services);
            resolverManager.popLocalVariablesNamespace();
        }
        RPAREN
; exception
        catch [SLTranslationException ex] {
        resolverManager.popLocalVariablesNamespace();
        throw ex;
        }   


quantifiedvardecls returns [Pair<KeYJavaType,ImmutableList<LogicVariable>> result = null]
                   throws SLTranslationException
{
    KeYJavaType t = null;
    ImmutableList<LogicVariable> vars = ImmutableSLList.<LogicVariable>nil();
    LogicVariable v = null;
}
:
	t=typespec v=quantifiedvariabledeclarator[t] 
	
	{ vars = vars.append(v); }
	
	(
	    COMMA v=quantifiedvariabledeclarator[t]
	    
	    { vars = vars.append(v); }
	)*
	{
	    result = new Pair<KeYJavaType,ImmutableList<LogicVariable>>(t, vars);
	}
;

boundvarmodifiers returns [boolean nullable = false] throws SLTranslationException
:
	NON_NULL | NULLABLE { nullable = true; }
;

typespec returns [KeYJavaType t = null] throws SLTranslationException
{
    int dim = 0;
}
:
	t=type 
	(
	    dim=dims
	    {
		String fullName = t.getFullName();
		for (int i=0; i < dim; i++) {
		    fullName += "[]";
		}
		t = javaInfo.getKeYJavaType(fullName);
	if(t == null && dim > 0) {
	    //try to create missing array type
	      try {
	    javaInfo.readJavaBlock("{" + fullName + " k;}");
	    t = javaInfo.getKeYJavaType(fullName);
	    } catch (Exception e) {
	    t = null;
		}
	    }
	    }
	)?
;

dims returns [int dimension = 0] throws SLTranslationException
:
	(LBRACKET RBRACKET { dimension++; } )+
    ;

type returns [KeYJavaType t = null] throws SLTranslationException
:
	(builtintype) => t=builtintype
    |
	t=referencetype
    |
	TYPE
	{
	    raiseNotSupported("\\TYPE");
	}
	
;

referencetype returns [KeYJavaType type = null] throws SLTranslationException
{
    String typename;
}
:
	typename=name
	{
	    try {
		type = resolverManager.resolve(null, typename, null).getType();
	    } catch (NullPointerException e) {
		raiseError("Type " + typename + " not found.");
	    }
	}
;   

builtintype returns [KeYJavaType type = null] throws SLTranslationException
:
	(
	    BYTE 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_BYTE);
	    }
	|
	    SHORT 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_SHORT);
	    }
	|
	    INT 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT);
	    }
	|
	    LONG 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_LONG);
	    }
	|
	    BOOLEAN 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
	    }
	|
	    VOID 
	    {
		type = KeYJavaType.VOID_TYPE;
	    }
	|
	    BIGINT
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_BIGINT);
	    } 
	|
	    REAL
	    {
		raiseNotSupported("\\real");
	    } 
        |   LOCSET
            {
                type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_LOCSET);
            }
        |   SEQ
            {
                type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_SEQ);
            }            
        | FREE { type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_FREE_ADT); }
	)
	
;

name returns [String result = ""] throws SLTranslationException
:
	id:IDENT
	{ result += id.getText(); }
	(
	    DOT id1:IDENT 
	    { result += "." + id1.getText(); }
	)*
;

quantifiedvariabledeclarator[KeYJavaType t] returns [LogicVariable v = null] throws SLTranslationException
{
    int dim = 0;
    KeYJavaType varType = null;
}
:
   id:IDENT (dim=dims)?
   {
	  if (dim > 0) {
	    String fullName;
	    if (t.getJavaType() instanceof ArrayType) {
		fullName = ((ArrayType) t.getJavaType()).getAlternativeNameRepresentation();
	    } else {
		fullName = t.getFullName();
	    }
	    for (int i=0; i < dim; i++) {
		fullName += "[]";
	    }
	    
	    varType = javaInfo.getKeYJavaType(fullName);
	  } else {
		  varType = t;
	  }
	  
	  v = new LogicVariable(new Name(id.getText()), varType.getSort());
   }
;

