parser grammar KeYJMLParser;

options {
    tokenVocab = KeYJMLLexer;
    k = 1;
}

@header {
    package de.uka.ilkd.key.speclang.jml.translation;

    import java.io.StringReader;

    import org.key_project.util.collection.*;
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
    import de.uka.ilkd.key.proof.OpReplacer;
    import de.uka.ilkd.key.speclang.HeapContext;
    import de.uka.ilkd.key.speclang.PositionedString;
    import de.uka.ilkd.key.speclang.translation.*;
    import de.uka.ilkd.key.util.Pair;
    import de.uka.ilkd.key.util.Triple;
    import de.uka.ilkd.key.util.InfFlowSpec;

    import java.math.BigInteger;
    import java.util.List;
    import java.util.Map;
    import java.util.LinkedHashMap;
    import java.util.ArrayList;
}

@members {

    private TermBuilder tb;

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


    private KeYJMLParser(KeYJMLLexer lexer,
		String fileName,
		Services services,
		KeYJavaType specInClass,
		ProgramVariable self,
		ImmutableList<ProgramVariable> paramVars,
		ProgramVariable result,
		ProgramVariable exc,
		Map<LocationVariable,Term> atPres) {
	this(new CommonTokenStream(lexer));

	// save parameters
	this.services       = services;
	this.tb             = services.getTermBuilder();
	this.javaInfo       = services.getJavaInfo();
	containerType  =   specInClass;
	this.intLDT         = services.getTypeConverter().getIntegerLDT();
	this.heapLDT        = services.getTypeConverter().getHeapLDT();
	this.locSetLDT      = services.getTypeConverter().getLocSetLDT();
	this.booleanLDT     = services.getTypeConverter().getBooleanLDT();
	this.excManager     = new SLTranslationExceptionManager(this,
				    				fileName,
				    				new Position(0,0));
        this.translator     = new JMLTranslator(excManager, fileName, services);

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

    static ANTLRStringStream createANTLRStringStream(PositionedString ps){
       ANTLRStringStream result = new ANTLRStringStream(ps.text);
       result.name = ps.fileName;
       result.setCharPositionInLine(ps.pos.getColumn());
       result.setLine(ps.pos.getLine() + 1);
       return result;
    }

    public KeYJMLParser(PositionedString ps,
		Services services,
		KeYJavaType specInClass,
		ProgramVariable self,
		ImmutableList<ProgramVariable> paramVars,
		ProgramVariable result,
		ProgramVariable exc,
		Map<LocationVariable,Term> atPres) {
	this(new KeYJMLLexer(createANTLRStringStream(ps)),
	     ps.fileName,
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
        List<PositionedString> res = new ArrayList<PositionedString>(warnings.size());
        res.addAll(translator.getWarnings());
        return res;
    }


    public Term parseExpression() throws SLTranslationException {
	Term result = null;

	try {
	    result = expression().getTerm();
	} catch (RecognitionException e) {
	    throw excManager.convertException(e);
	}

	return tb.convertToFormula(result);
    }


    public ImmutableList<ProgramVariable> parseVariableDeclaration() throws SLTranslationException {

	Pair<KeYJavaType,ImmutableList<LogicVariable>> vars;
	try {
	    vars = quantifiedvardecls();
	} catch (RecognitionException e) {
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

	private LocationVariable getPermissionHeap() {
		return services.getTypeConverter().getHeapLDT().getPermissionHeap();
	}

    /**
     * Converts a term so that all of its non-rigid operators refer to the pre-state.
     */
    // TODO: remove when all clients have been moved to JMLTranslator
    private Term convertToOld(final Term term) {
	    assert atPres != null && atPres.get(getBaseHeap()) != null;
	    Map<Term, Term> map = new LinkedHashMap<Term, Term>();
        for (LocationVariable var : atPres.keySet()) {
            // caution: That may now also be other variables than only heaps.
            Term varAtPre = atPres.get(var);
            if (varAtPre != null) {
                map.put(tb.var(var), varAtPre);
            }
        }
	    OpReplacer or = new OpReplacer(map, tb.tf());
	    return or.replace(term);
    }

    private Term convertToBackup(Term term) {
	assert atPres != null && atPres.get(getSavedHeap()) != null;
	Map map = new LinkedHashMap();
	map.put(tb.var(getBaseHeap()), tb.var(getSavedHeap()));
        if(atPres.get(getBaseHeap()) != null) {
	  map.put(atPres.get(getBaseHeap()), atPres.get(getSavedHeap()));
        }
	OpReplacer or = new OpReplacer(map, tb.tf());
	return or.replace(term);
    }

    private Term convertToPermission(Term term) throws SLTranslationException {
        LocationVariable permissionHeap = getPermissionHeap();
        if(permissionHeap == null) {
           raiseError("\\permission expression used in a non-permission context and permissions not enabled.");
        }
        if(!term.op().name().toString().endsWith("::select")) {
           raiseError("\\permission expression used with non store-ref expression.");
        }
        return tb.select(services.getTypeConverter().getPermissionLDT().targetSort(), tb.var(getPermissionHeap()), term.sub(1), term.sub(2));
    }

    private String createSignatureString(ImmutableList<SLExpression> signature) {
	if (signature == null || signature.isEmpty()) {
	    return "";
	}
	String sigString = "";

	for(SLExpression expr : signature) {
	    final KeYJavaType t = expr.getType();
	    sigString += (t==null? "<unknown type>": t.getFullName()) + ", ";
	}

	return sigString.substring(0, sigString.length() - 2);
    }


    private SLExpression lookupIdentifier(String lookupName,
					  SLExpression receiver,
					  SLParameters params,
					  Token t)
				       throws SLTranslationException {

	// Identifier with suffix in parentheses? Probably a method call
	// parse in the parameter list and call again
    if (input.LA(1) == LPAREN) {
    	return receiver;
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
    
    // Helper variable, which is necessary because antlr doesn't forward local variables to generated DFAs.
    // It is used in a semantic predicate to determine the branch that will be taken by the generated DFA.
    private boolean representsClauseLhsIsLocSet;


    /* ---- antlr stuff ---- (Exception handling) */

    @Override
    public void reportError(RecognitionException ex) {
        // dont do anything
    }

    public void recover(IntStream input, RecognitionException re) {
        throw new RuntimeException(re);
    }

    /** Not currently used */
    @Override
    public Object recoverFromMismatchedSet(IntStream input,
            RecognitionException e, BitSet follow) throws RecognitionException {
        // comment says it is never used, still make sure ...
        throw e;
    }

    protected Object recoverFromMismatchedToken(IntStream input, int ttype,
            BitSet follow) throws RecognitionException {
        throw new MismatchedTokenException(ttype, input);
    }
    
    protected void mismatch(IntStream input, int ttype, BitSet follow) throws RecognitionException
    {
        throw new MismatchedTokenException(ttype, input);
    }

}

@rulecatch {
    catch(RecognitionException re) {
        throw re;
    }
}

top returns [Object ret = null] throws  SLTranslationException
:
    (   accessibleclause { ret = $accessibleclause.ret; }
    |   assignableclause { ret = $assignableclause.ret; }
    |   breaksclause { ret = $breaksclause.result; }
    |   continuesclause { ret = $continuesclause.result; }
    |   dependsclause { ret = $dependsclause.result; }
    |   ensuresclause { ret = $ensuresclause.ret; }
    |   ensuresfreeclause { ret = $ensuresfreeclause.ret; }
    |   representsclause { ret = $representsclause.result; }
    |   axiomsclause { ret = $axiomsclause.ret; }
    |   requiresclause { ret = $requiresclause.ret; }
    |   joinprocclause { ret = $joinprocclause.ret; }
    |   requiresfreeclause { ret = $requiresfreeclause.ret; }
    |   decreasesclause { ret = $decreasesclause.ret; }
    |   separatesclause { ret = $separatesclause.result; } // old information flow syntax
    |   determinesclause { ret = $determinesclause.result; } // new information flow syntax
    |   loopseparatesclause { ret = $loopseparatesclause.result; } // old information flow syntax
    |   loopdeterminesclause { ret = $loopdeterminesclause.result; } // new information flow syntax
    |   returnsclause { ret = $returnsclause.ret; }
    |   signalsclause { ret = $signalsclause.ret; }
    |   signalsonlyclause { ret = $signalsonlyclause.result; }
    |   termexpression { ret = $termexpression.result; }
    )
    (SEMI)? EOF
    ;

accessibleclause returns [Term ret = null] throws SLTranslationException
@after{ ret = result; }
:
    acc=ACCESSIBLE result=storeRefUnion
        { result = translator.translate(acc.getText(), Term.class, result, services); }
    ;


assignableclause returns [Term ret = null] throws SLTranslationException
@after{ ret = result; }
:
    ass=ASSIGNABLE
    ( result=storeRefUnion
        { result = translator.translate(ass.getText(), Term.class, result, services); }
    | STRICTLY_NOTHING
        { result = tb.strictlyNothing(); }
    )
    ;


dependsclause returns [Triple<ObserverFunction,Term,Term> result=null] throws SLTranslationException
:
    dep=DEPENDS lhs=expression
    COLON rhs=storeRefUnion
    (MEASURED_BY mby=expression)? SEMI
        { result = translator.translate(
                dep.getText(), Triple.class, lhs, rhs, mby, services); }
    ;

decreasesclause returns [Term ret = null] throws SLTranslationException
@after{ret=result;}
:
    dec=DECREASES result=termexpression
        (COMMA t=termexpression { result = tb.pair(result, t); } )*
    ;

requiresclause returns [Term ret = null] throws SLTranslationException
:
    req=REQUIRES result=predornot
            { ret = translator.translate(req.getText(), Term.class, result, services); }
    ;

requiresfreeclause returns [Term ret = null] throws SLTranslationException
:
    req=REQUIRES_FREE result=predornot
            { ret = translator.translate(req.getText(), Term.class, result, services); }
    ;

joinprocclause returns [Term ret = null] throws SLTranslationException
:
    jpr=JOIN_PROC result=predornot
            { ret = translator.translate(jpr.getText(), Term.class, result, services); }
    ;

ensuresclause returns [Term ret = null] throws SLTranslationException
:
    ens=ENSURES result=predornot
            { ret = translator.translate(ens.getText(), Term.class, result, services); }
    ;

ensuresfreeclause returns [Term ret = null] throws SLTranslationException
:
    ens=ENSURES_FREE result=predornot
            { ret = translator.translate(ens.getText(), Term.class, result, services); }
    ;

axiomsclause returns [Term ret = null] throws SLTranslationException
:
    axm=MODEL_METHOD_AXIOM result=termexpression
            { ret = translator.translate(axm.getText(), Term.class, result, services); }
    ;

representsclause returns [Pair<ObserverFunction,Term> result=null] throws SLTranslationException
:
    rep=REPRESENTS lhs=expression {representsClauseLhsIsLocSet = lhs.getTerm().sort().equals(locSetLDT.targetSort());}
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
        (
        (LARROW | EQUAL_SINGLE)
        (
        { !representsClauseLhsIsLocSet}?
             rhs=expression
            {   // TODO: move code out of the parser!
                if(!rhs.isTerm()) {
                    raiseError("Represents clause with unexpected rhs: " + rhs);
                }
                Term rhsTerm = rhs.getTerm();
                if(rhsTerm.sort() == Sort.FORMULA) {
                    rhsTerm = tb.ife(rhsTerm, tb.TRUE(), tb.FALSE());
                }
                t = tb.equals(lhs.getTerm(), rhsTerm);
            }
        |
            t=storeRefUnion
            {   // TODO: move code out of the parser!
                t = tb.equals(lhs.getTerm(), t);
            }
        ))
        |
        (
            SUCH_THAT t=predicate
        )
    )
    { result = translator.translate(rep.getText(), Pair.class, lhs, t, services); }
    ;


separatesclause returns  [InfFlowSpec result = InfFlowSpec.EMPTY_INF_FLOW_SPEC] throws SLTranslationException
@init {
    ImmutableList<Term> decl = ImmutableSLList.<Term>nil();
    ImmutableList<Term> erases = ImmutableSLList.<Term>nil();
    ImmutableList<Term> newObs = ImmutableSLList.<Term>nil();
}
:
    SEPARATES (NOTHING | sep = infflowspeclist)
    (   (DECLASSIFIES (NOTHING | tmp = infflowspeclist {decl = decl.append(tmp);})) |
        (ERASES (NOTHING | tmp = infflowspeclist {erases = erases.append(tmp);})) |
        (NEW_OBJECTS (NOTHING | tmp = infflowspeclist {newObs = newObs.append(tmp);}))
    )*
    {decl = sep.append(decl);
     erases = sep.append(erases);
     result = new InfFlowSpec(decl, erases, newObs);}
    ;


loopseparatesclause returns  [InfFlowSpec result = InfFlowSpec.EMPTY_INF_FLOW_SPEC] throws SLTranslationException
@init {
    ImmutableList<Term> sep = ImmutableSLList.<Term>nil();
    ImmutableList<Term> newObs = ImmutableSLList.<Term>nil();
}
:
    LOOP_SEPARATES (NOTHING | tmp = infflowspeclist {sep=tmp;})
    (   (NEW_OBJECTS (NOTHING | tmp = infflowspeclist {newObs = newObs.append(tmp);}))
    )*
    {result = new InfFlowSpec(sep, sep, newObs);}
    ;


determinesclause returns  [InfFlowSpec result = InfFlowSpec.EMPTY_INF_FLOW_SPEC] throws SLTranslationException
@init {
    ImmutableList<Term> decl = ImmutableSLList.<Term>nil();
    ImmutableList<Term> erases = ImmutableSLList.<Term>nil();
    ImmutableList<Term> newObs = ImmutableSLList.<Term>nil();
}
:
    DETERMINES (NOTHING {det=ImmutableSLList.<Term>nil();} | det = infflowspeclist)
    BY (NOTHING {by = ImmutableSLList.<Term>nil();} | (ITSELF {by = det;}) | by = infflowspeclist)
    (   (DECLASSIFIES (NOTHING | tmp = infflowspeclist {decl = decl.append(tmp);})) |
        (ERASES (NOTHING | tmp = infflowspeclist {erases = erases.append(tmp);})) |
        (NEW_OBJECTS (NOTHING | tmp = infflowspeclist {newObs = newObs.append(tmp);}))
    )*
    {det = det.append(erases);
     by = by.append(decl);
     result = new InfFlowSpec(by, det, newObs);}
    ;


loopdeterminesclause returns  [InfFlowSpec result = InfFlowSpec.EMPTY_INF_FLOW_SPEC] throws SLTranslationException
@init {
    ImmutableList<Term> newObs = ImmutableSLList.<Term>nil();
}
:
    LOOP_DETERMINES (NOTHING | det = infflowspeclist)
    BY ITSELF
    (   (NEW_OBJECTS (NOTHING | tmp = infflowspeclist {newObs = newObs.append(tmp);}))
    )*
    {result = new InfFlowSpec(det, det, newObs);}
    ;


infflowspeclist returns  [ImmutableList<Term> result = ImmutableSLList.<Term>nil()] throws SLTranslationException
:
    term = termexpression { result = result.append(term); }
    (COMMA term = termexpression { result = result.append(term); })*
        { result = translator.translate("infflowspeclist", ImmutableList.class, result, services); }
    ;


signalsclause returns [Term ret=null] throws SLTranslationException
@init {
    Term pred = null;
    String vName = null;
    LogicVariable eVar = null;
}
@after{ret=result;}
:
	sig=SIGNALS LPAREN excType=referencetype (id=IDENT { vName = id.getText(); })? RPAREN
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


signalsonlyclause returns [Term result = null] throws SLTranslationException
@init {
    ImmutableList<KeYJavaType> typeList = ImmutableSLList.<KeYJavaType>nil();
    KeYJavaType type = null;
}
:
    sigo=SIGNALS_ONLY
    (   NOTHING
      | rtype = referencetype { typeList = typeList.append(rtype); }
        (COMMA rtype = referencetype { typeList = typeList.append(rtype); })*
    )
    { result = translator.translate(sigo.getText(), Term.class, typeList, this.excVar, services); }
    ;


termexpression returns [Term result = null] throws SLTranslationException
:
    exp=expression { result = (Term) exp.getTerm(); }
    ;


breaksclause returns [Pair result=null] throws SLTranslationException
@init {
    String label = null;
}
:
	breaks=BREAKS LPAREN (id=IDENT { label = id.getText(); })? RPAREN
	(pred = predornot)?
	{
        result = translator.translate(breaks.getText(), Pair.class, pred, label, services);
	}
;


continuesclause returns [Pair result=null] throws SLTranslationException
@init {
    String label = null;
}
:
	continues=CONTINUES LPAREN (id=IDENT { label = id.getText(); })? RPAREN
	(pred = predornot)?
	{
        result = translator.translate(continues.getText(), Pair.class, pred, label, services);
	}
	;


returnsclause returns [Term ret=null] throws SLTranslationException
@after{ret=result;}
:
	rtrns=RETURNS
	(result = predornot)?
	{
        result = translator.translate(rtrns.getText(), Term.class, result, services);
	}
    ;


storeRefUnion returns [Term result = null] throws SLTranslationException
:   list = storeRefList
    { result = tb.union(list); };


storeRefList returns [ImmutableList<Term> result = ImmutableSLList.<Term>nil()] throws SLTranslationException
:   t = storeref { result = result.append(t); }
	(COMMA t = storeref { result = result.append(t); } )*;



storeRefIntersect returns [Term result = null] throws SLTranslationException
:   list = storeRefList { result = tb.intersect(list); };


storeref returns [Term ret = null] throws SLTranslationException
@after{ret=result;}
:       NOTHING { result = tb.empty(); }
    |   EVERYTHING { result = tb.createdLocs(); }
    |   NOT_SPECIFIED { result = tb.createdLocs(); }
    |   result = storeRefExpr;


createLocset returns [Term result = null] throws SLTranslationException
:
    (LOCSET | SINGLETON) LPAREN list=exprList RPAREN
    {
        result = translator.translate("create locset", Term.class, list, services);
    }
    ;


exprList returns [ImmutableList<SLExpression> result = ImmutableSLList.<SLExpression>nil()] throws SLTranslationException
:   expr = expression { result = result.append(expr); }
	(COMMA expr = expression { result = result.append(expr); } )*;


storeRefExpr returns [Term result = null] throws SLTranslationException
:
    expr=expression
    {
        result = translator.translate("store_ref_expr", Term.class, expr, services);
    }
    ;


specarrayrefexpr[SLExpression receiver, String fullyQualifiedName, Token lbrack]
               returns [SLExpression result = null]
               throws SLTranslationException
:
    (
	( rangeFrom=expression (DOTDOT rangeTo=expression)? )
	| MULT
    )
    {
        result = translator.translate("array reference", SLExpression.class, services, receiver, fullyQualifiedName, lbrack, rangeFrom, rangeTo);
    }
;


predornot returns [Term ret=null] throws SLTranslationException
@after{ ret = result; }
:
	result=predicate
    |   n=NOT_SPECIFIED
        { result = translator.createSkolemExprBool(n).getTerm(); }
    |   SAME
    ;

predicate returns [Term result=null] throws SLTranslationException
:
	expr=expression
	{
	    if(!expr.isTerm() && expr.getTerm().sort() == Sort.FORMULA) {
	        raiseError("Expected a formula: " + expr);
	    }
	    result = expr.getTerm();
	}
    ;


expression returns [SLExpression ret=null] throws SLTranslationException
:
	result=conditionalexpr
	{
	    if(!result.isTerm()) {
	        raiseError("Expected a term: " + result);
	    }
	    ret = result;
	}
    ;

conditionalexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
:
	result=equivalenceexpr
	(
	    QUESTIONMARK a=conditionalexpr COLON b=conditionalexpr
	    {
	    	result = translator.translate(JMLTranslator.JMLKeyWord.CONDITIONAL, services, result, a, b);
	    }
	)?
    ;


equivalenceexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
:
	result = impliesexpr
        (   eq=EQV_ANTIV right=impliesexpr
            { result = translator.translate(eq.getText(), SLExpression.class, result, right, services); }
        )*
    ;

/*
 * Note: According to JML Manual 12.6.3 forward implication has to be parsed right-associatively
 * and backward implication left-associatively.
 */
impliesexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
:
	result=logicalorexpr
	(
	    IMPLIES expr=impliesforwardexpr
	    {
		result = new SLExpression(tb.imp(tb.convertToFormula(result.getTerm()),
		                                 tb.convertToFormula(expr.getTerm())));
	    }

	  |
	    (
		IMPLIESBACKWARD expr=logicalorexpr
		{
		result = new SLExpression(tb.imp(tb.convertToFormula(expr.getTerm()),
		                                 tb.convertToFormula(result.getTerm())));
		}
	    )+
	)?
;

impliesforwardexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
:
	result=logicalorexpr
	(
	    IMPLIES expr=impliesforwardexpr
	    {
		result = new SLExpression(tb.imp(tb.convertToFormula(result.getTerm()),
		                                 tb.convertToFormula(expr.getTerm())));
	    }
	)?
;

logicalorexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
:
	result=logicalandexpr
	(
	    LOGICALOR expr=logicalandexpr
	    {
	        result = new SLExpression(tb.orSC(tb.convertToFormula(result.getTerm()),
                                                  tb.convertToFormula(expr.getTerm())));
	    }
	)*
;

logicalandexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
:
	result=inclusiveorexpr
	(
	    LOGICALAND expr=inclusiveorexpr
	    {
		result = new SLExpression(tb.andSC(tb.convertToFormula(result.getTerm()),
                                                   tb.convertToFormula(expr.getTerm())));
	    }
	)*
;


inclusiveorexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
:
	result=exclusiveorexpr
	(
	    INCLUSIVEOR expr=exclusiveorexpr
	    {
	       if(intHelper.isIntegerTerm(result)) {
                   result = intHelper.buildPromotedOrExpression(result,expr);
               } else {
                   result = new SLExpression(tb.or(tb.convertToFormula(result.getTerm()),
                                                   tb.convertToFormula(expr.getTerm())));
               }
	    }
	)*
;


exclusiveorexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
:
	result=andexpr
	(
	    XOR expr=andexpr
	    {
	       if(intHelper.isIntegerTerm(result)) {
                   result = intHelper.buildPromotedXorExpression(result,expr);
               } else {
                   Term resultFormula = tb.convertToFormula(result.getTerm());
                   Term exprFormula = tb.convertToFormula(expr.getTerm());
                   result = new SLExpression(tb.or(tb.and(resultFormula, tb.not(exprFormula)),
                                                   tb.and(tb.not(resultFormula), exprFormula)));
               }
	    }
	)*
;


andexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
:
	result=equalityexpr
	{
	    if(!result.isTerm()) {
		raiseError("Found a type where only a term is allowed: "
			   + result);
	    }
	}
	(
	    AND expr=equalityexpr
	    {
	       if(intHelper.isIntegerTerm(result)) {
                   result = intHelper.buildPromotedAndExpression(result, expr);
               } else {
                   result = new SLExpression(tb.and(tb.convertToFormula(result.getTerm()),
                                                    tb.convertToFormula(expr.getTerm())));
               }
	    }
	)*
;

equalityexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
	 :
	result=relationalexpr
	(   eq=EQ_NEQ right=relationalexpr
	        { result = translator.translate(eq.getText(), SLExpression.class, result, right, services); }
	)*
;

relationalexpr returns [SLExpression ret=null] throws SLTranslationException
@init {
    Function f = null;
    KeYJavaType type = null;
    Token opToken = null;
}
@after{ret=result;}
:
	result=shiftexpr
	(
	    lt=LT right=shiftexpr 
	    // allow range predicates of the shape 0 < x < 23 (JML extension)
	    ( LT right2=shiftexpr )?
	    {
		f = intLDT.getLessThan();
		opToken = lt;
	    }
	|
	    gt=GT right=shiftexpr
	    {
		f = intLDT.getGreaterThan();
		opToken = gt;
	    }
	|
	    leq=LEQ right=shiftexpr
	    // allow range predicates of the shape 0 <= x < 23 (JML extension)
	    ( LT right2=shiftexpr )?
	    {
		f = intLDT.getLessOrEquals();
		opToken = leq;
	    }
	|
	    geq=GEQ right=shiftexpr
	    {
		f = intLDT.getGreaterOrEquals();
		opToken = geq;
	    }
	|
	    llt=LOCKSET_LT right=postfixexpr
	    {
	        addIgnoreWarning("Lockset ordering is not supported",llt);
	        final Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
	        f = new Function(new Name("lockset_lt"), Sort.FORMULA, objSort, objSort);
	        opToken = llt;
	    }
	|
	    lleq=LOCKSET_LEQ right=postfixexpr
	    {
	        addIgnoreWarning("Lockset ordering is not supported",lleq);
	        final Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
	        f = new Function(new Name("lockset_leq"), Sort.FORMULA, objSort, objSort);
	        opToken = lleq;
	    }
	|
	    io=INSTANCEOF rtype=typespec
	    {
		f = rtype.getSort().getInstanceofSymbol(services);
		opToken = io;
	    }
	|
	    st=ST right=shiftexpr
	    {
		if (result.isTerm() || right.isTerm()) {
		    raiseError("Cannot build subtype expression from terms.", st);
		}
		assert result.isType();
		assert right.isType();

		if (result.getTerm() == null) {
		    addIgnoreWarning("subtype expression <: only supported for" +
			" \\typeof() arguments on the left side.", st);
			final Namespace fns = services.getNamespaces().functions();
			int x = -1; Name name = null;
			do name = new Name("subtype_"+ ++x);
			while (fns.lookup(name)!= null);
			final Function z = new Function(name,Sort.FORMULA);
			fns.add(z);
			result = new SLExpression(tb.func(z));
		} else {

		Sort os = right.getType().getSort();
		Function ioFunc = os.getInstanceofSymbol(services);

		result = new SLExpression(
		    tb.equals(
			tb.func(ioFunc, result.getTerm()),
			tb.TRUE()));
	    }
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
				tb.and(tb.not(tb.equals(result.getTerm(), tb.NULL())),
				       tb.equals(tb.func(f, result.getTerm()), tb.TRUE())));
			} else {
			    if (right.isType()) {
			    raiseError("Cannot build relational expression from type " +
				right.getType().getName() + ".", opToken);
			    }
			    assert right.isTerm();

			    result = new SLExpression(
				tb.func(f,result.getTerm(),right.getTerm()));
			} 
			if (right2 != null) { // range expressions like 0 <= x < 23
			    if (right2.isType()) {
			    raiseError("Cannot build relational expression from type " +
				right2.getType().getName() + ".", opToken);
			    }
			    assert right2.isTerm();
			    final Term upperBound = tb.func(intLDT.getLessThan(),right.getTerm(),right2.getTerm());
			    result = new SLExpression(tb.and(result.getTerm(),upperBound));
			}
		} catch (TermCreationException e) {
		    raiseError("Error in relational expression: " + e.getMessage());
		} catch (IllegalArgumentException e) {
		    raiseError("Internal error.");
		}
	    }
	}
;

shiftexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret=result;}
:
    result=additiveexpr
    (
	sr=SHIFTRIGHT e=additiveexpr
	{
        result = translator.<SLExpression>translate(sr.getText(), SLExpression.class, services, result, e);
	}
    |
	sl=SHIFTLEFT e=additiveexpr
	{
        result = translator.<SLExpression>translate(sl.getText(), SLExpression.class, services, result, e);
	}
    |
	usr=UNSIGNEDSHIFTRIGHT e=additiveexpr
	{
        result = translator.<SLExpression>translate(usr.getText(), SLExpression.class, services, result, e);
	}
    )*
;


additiveexpr returns [SLExpression ret=null] throws SLTranslationException
@after{ret = result;}
:
    result=multexpr
    (
	plus=PLUS e=multexpr
	{
        result = translator.<SLExpression>translate(plus.getText(), SLExpression.class, services, result, e);
	}
    |
	minus=MINUS e=multexpr
	{
	    result = translator.<SLExpression>translate(minus.getText(), SLExpression.class, services, result, e);
	}
    )*
;


multexpr returns [SLExpression ret=null] throws SLTranslationException
@after {ret = result;}
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


unaryexpr returns [SLExpression ret=null] throws SLTranslationException
@after {ret = result;}
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

castexpr returns  [SLExpression ret = null] throws SLTranslationException
@init {
    KeYJavaType type = null;
}
:
LPAREN rtype=typespec RPAREN result=unaryexpr
{
    ret = translator.translate(JMLTranslator.JMLKeyWord.CAST, services, intHelper, rtype, result);
}
;

unaryexprnotplusminus returns [SLExpression ret=null] throws SLTranslationException
@after {ret = result;}
:
	NOT e=unaryexpr
	{
	    if (e.isType()) {
		raiseError("Cannot negate type " + e.getType().getName() + ".");
	    }

	    Term t = e.getTerm();
	    assert t != null;

	    if (t.sort() == Sort.FORMULA) {
		result = new SLExpression(tb.not(t));
	    } else if(t.sort() == booleanLDT.targetSort()) {
		result = new SLExpression(tb.not(tb.equals(t, tb.TRUE())));
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


postfixexpr returns [SLExpression ret=null] throws SLTranslationException
@init {
    String fullyQualifiedName = "";
    SLExpression result=null;
}
@after { ret = result; }
:
	expr=primaryexpr
	{
	    fullyQualifiedName = input.LT(-1).getText();
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
		fullyQualifiedName += "." + input.LT(-1).getText();
	    }
	)*

	{
	    if (expr == null) {
		raiseError("Expression " + fullyQualifiedName + " cannot be resolved.");
	    }
	    result = expr; //.getTerm();
	}
;

primaryexpr returns [SLExpression ret=null] throws SLTranslationException
@init {
    Term s1, s2;
}
@after {ret = result;}
:
	result = constant
    |   id=IDENT     { result = lookupIdentifier(id.getText(), null, null, id); }
    |   inv=INV      { result = translator.translate(inv.getText(),services,
                                selfVar==null? null: tb.var(selfVar),containerType);}
    |   TRUE         { result = new SLExpression(tb.tt()); }
    |   FALSE        { result = new SLExpression(tb.ff()); }
    |   NULL         { result = new SLExpression(tb.NULL()); }
    |   result=jmlprimary
    |   THIS
        {
            if(selfVar == null) {
            	raiseError("Cannot access \"this\" in a static context!");
            }
            try {
                result = new SLExpression(tb.var(selfVar), selfVar.getKeYJavaType());
            } catch (Throwable e) { raiseError(e.getMessage()); }
        }
    |   new_expr
    |   array_initializer
;

transactionUpdated
  returns [SLExpression result=null]
  throws SLTranslationException
@init {
   String fieldName = "<transactionConditionallyUpdated>";
}
:

   tk=TRANSACTIONUPDATED LPAREN expr=expression RPAREN
   {
      result = lookupIdentifier(fieldName, expr, null, tk);
   }
;

primarysuffix[SLExpression receiver, String fullyQualifiedName]
		returns [SLExpression ret=null]
		throws SLTranslationException
@init {
    String lookupName = null;
}
@after { ret = result; }
:
{
    lookupName = fullyQualifiedName;
}
( DOT
    ( id=IDENT
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
    | tr=TRANSIENT
    {
        result = lookupIdentifier("<transient>", receiver, null, tr);
    }
    |    
     THIS
    {
    	result = new SLExpression(
    		services.getTypeConverter().findThisForSort(receiver.getType().getSort(),
    							    tb.var(selfVar),
    							    javaInfo.getKeYJavaType(selfVar.sort()),
    							    true),
                receiver.getType());
    }
    | INV
    {
        result = translator.translate("\\inv",services,receiver.getTerm(),receiver.getType());
    }
    | MULT
         {
	     result = new SLExpression(tb.allFields(receiver.getTerm()),
	                               javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
         }
   )
    |
	l=LPAREN (params=expressionlist)? RPAREN
	{
            ImmutableList<SLExpression> preHeapParams = ImmutableSLList.<SLExpression>nil();
            for(LocationVariable heap : HeapContext.getModHeaps(services, false)) {
              Term p;
              if(atPres == null || atPres.get(heap) == null) { p = tb.var(heap); } else { p = atPres.get(heap); }
              preHeapParams = preHeapParams.append(new SLExpression(p));
            }
            params = (params == null) ? preHeapParams : params.prepend(preHeapParams);

	    lookupName = lookupName.substring(lookupName.lastIndexOf('.')+1);

	    result = lookupIdentifier(lookupName, receiver, new SLParameters(params), l);
	    if (result == null) {
		raiseError("Method " + lookupName + "("
		           + createSignatureString(params) + ") not found!", l);
	    }
            if(((IProgramMethod)result.getTerm().op()).getStateCount() > 1 &&
               (atPres == null || atPres.get(getBaseHeap()) == null)) {
               raiseError("Two-state model method " + lookupName + " not allowed in this context!", l);
            }

	}
    |
	lbrack=LBRACKET result=specarrayrefexpr[receiver, fullyQualifiedName, lbrack] RBRACKET

)
;

new_expr throws SLTranslationException
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
:
    LBRACKET (length=expression)? RBRACKET
;

array_initializer throws SLTranslationException
:
    LBRACE init=expressionlist RBRACE
    {
        raiseNotSupported("array initializer");
    }
;

expressionlist returns [ImmutableList<SLExpression> result=ImmutableSLList.<SLExpression>nil()]
               throws SLTranslationException
:
	expr=expression { result = result.append(expr); } (COMMA expr=expression {result = result.append(expr);} )*
;

constant returns [SLExpression ret=null] throws SLTranslationException
:
	result=javaliteral { ret = result; }
;

javaliteral returns [SLExpression ret=null] throws SLTranslationException
@after{ ret = result; }
:
	result=integerliteral
    |
	l=STRING_LITERAL
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
	    Term stringTerm = tb.func(strPool, charListTerm);
	    return new SLExpression(stringTerm,
	                            javaInfo.getKeYJavaType("java.lang.String"));
	}
    |
	CHAR_LITERAL
	{
	    raiseNotSupported("character literals");
	}
    ;

integerliteral returns [SLExpression ret=null] throws SLTranslationException
@after {ret = result;}
:
	result=decimalintegerliteral
    |
	result=hexintegerliteral
;

hexintegerliteral returns [SLExpression result=null] throws SLTranslationException
:
    n=HEXNUMERAL
    {
	BigInteger decInteger = new BigInteger(n.getText().substring(2), 16);
	result = new SLExpression(tb.zTerm(decInteger.toString()),
	                          javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT));
    }
;

decimalintegerliteral returns [SLExpression ret=null] throws SLTranslationException
:
	result=decimalnumeral{ret = result;}
;

decimalnumeral returns [SLExpression result=null] throws SLTranslationException
:
    n=DIGITS
    {
	result = new SLExpression(tb.zTerm(n.getText()),
	                          javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT));
    }
;

jmlprimary returns [SLExpression ret=null] throws SLTranslationException
@after {ret = result;}
:
	RESULT
	{
	    if(resultVar==null) {
		raiseError("\\result used in wrong context");
	    } else
	    result = new SLExpression(tb.var(resultVar), resultVar.getKeYJavaType());
	}
    |
	(LPAREN quantifier) => result=specquantifiedexpression
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
        PERMISSION LPAREN result=expression RPAREN
        {
            result = new SLExpression(convertToPermission(result.getTerm()));
        }
    |
	NONNULLELEMENTS LPAREN result=expression RPAREN
	{
	    t = result.getTerm();
	    Term resTerm = tb.not(tb.equals(t, tb.NULL()));

	    if (t.sort() instanceof ArraySort) {
		LogicVariable i = new LogicVariable(new Name("i"), javaInfo
				.getKeYJavaType(PrimitiveType.JAVA_INT)
				.getSort());

		// See JML reference manual
		// http://www.cs.iastate.edu/~leavens/JML/jmlrefman/jmlrefman_11.html#SEC139
		Term range = tb.and(
		    tb.leq(tb.zero(), tb.var(i)),
		    tb.lt(tb.var(i), tb.dotLength(t)));
		Term body = tb.equals(tb.dotArr(t, tb.var(i)), tb.NULL());
		body = tb.not(body);
		body = tb.imp(range, body);

		result = new SLExpression(tb.and(resTerm, tb.all(i, body)));
	    } else {
	        raiseError("\\nonnullelements may only be applied to arrays");
	    }
	}

    |   desc=INFORMAL_DESCRIPTION
	{
	    result = translator.translate("(* *)", SLExpression.class, services, desc,
	        selfVar, resultVar, paramVars, atPres == null ? null : atPres.get(getBaseHeap()));
	}

    |   escape=DL_ESCAPE ( (LPAREN) => LPAREN ( list=expressionlist )? RPAREN )?
        {
            result = translator.translate("\\dl_", SLExpression.class, escape, list, services);
        }
        
    |   mapEmpty=MAPEMPTY { result = translator.translateMapExpressionToJDL(mapEmpty,list,services); }
        
    |   tk=mapExpression LPAREN ( list=expressionlist )? RPAREN
		{
		    result = translator.translateMapExpressionToJDL(tk,list,services);
		}

    |   s2m=SEQ2MAP LPAREN ( list=expressionlist )? RPAREN
		{
		    result = translator.translateMapExpressionToJDL(s2m,list,services);
		}

    |   NOT_MODIFIED LPAREN t=storeRefUnion RPAREN
        {
        result = new SLExpression(translator.translate("\\not_modified", Term.class, services, atPres == null ? null : atPres.get(getBaseHeap()), t));
        }
    |   na=NOT_ASSIGNED LPAREN t=storeRefUnion RPAREN
        {
        result = translator.createSkolemExprBool(na);
        }

    // TODO: add \only_*

    |   FRESH LPAREN list=expressionlist RPAREN
	{
        result = translator.translate("\\fresh", SLExpression.class, list, atPres, services);
	}

    |   REACH LPAREN t=storeref COMMA e1=expression COMMA e2=expression (COMMA e3=expression)? RPAREN
	{
        result = translator.translate("reach", SLExpression.class, t, e1, e2, e3, services);
	}

    |   REACHLOCS LPAREN t=storeref COMMA e1=expression (COMMA e3=expression)? RPAREN
	{
        result = translator.translate("reachLocs", SLExpression.class, t, e1, e3, services);
	}

    |   duration=DURATION LPAREN result=expression RPAREN
	{
	    result = translator.createSkolemExprLong(duration,services);
	}

    |   space=SPACE LPAREN result=expression RPAREN
	{
	    result = translator.createSkolemExprLong(space,services);
	}

    |   wspace=WORKINGSPACE LPAREN result=expression RPAREN
	{
	    result = translator.createSkolemExprLong(wspace,services);
	}

    |   (MAX) => max=MAX LPAREN result=expression RPAREN
    {
        result = translator.createSkolemExprObject(max,services);
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

    |   lockset=LOCKSET
	{
	    result = translator.createSkolemExprObject(lockset,services);
	}

    |   IS_INITIALIZED LPAREN typ=referencetype RPAREN
	{
	    Term resTerm = tb.equals(
		tb.var(
		    javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED,
					  typ)),
		tb.TRUE());
	    result = new SLExpression(resTerm);
	}

    |   INVARIANT_FOR LPAREN result=expression RPAREN
	{
	    result = translator.translate("\\invariant_for", SLExpression.class, services, result);

	}

	|   STATIC_INVARIANT_FOR LPAREN typ=referencetype RPAREN
	{
	    result = translator.translate("\\static_invariant_for", SLExpression.class, services, typ);
	}

    |   ( LPAREN LBLNEG ) => LPAREN lblneg=LBLNEG IDENT result=expression RPAREN
	{
	    addIgnoreWarning("\\lblneg",lblneg);
	}

    |   ( LPAREN LBLPOS ) => LPAREN lblpos=LBLPOS IDENT result=expression RPAREN
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
            return new SLExpression(tb.equals(tb.func(strContent, e1.getTerm()),
                                              tb.func(strContent, e2.getTerm())));
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
            result = new SLExpression(tb.setMinus(t, t2),
                                      javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
        }

    |   ALLFIELDS LPAREN e1=expression RPAREN
        {
            if(!e1.isTerm() || !e1.getTerm().sort().extendsTrans(services.getJavaInfo().objectSort())) {
                raiseError("Invalid argument to \\allFields: " + e1);
            }
            result = new SLExpression(tb.allFields(e1.getTerm()),
                                      javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
        }

    |  ALLOBJECTS LPAREN t=storeref RPAREN
        {
            result = new SLExpression(tb.allObjects(t.sub(1)),
                                      javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
        }
    |   UNIONINF
        LPAREN
        (nullable=boundvarmodifiers)?
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
               result = translator.translate(JMLTranslator.JMLKeyWord.UNIONINF, nullable, declVars, t, t2, services);
        }

    |   pd=DISJOINT LPAREN tlist=storeRefList RPAREN {
            result = translator.translate(pd.getText(), SLExpression.class, tlist, services);
        }

    |   SUBSET LPAREN t=storeref COMMA t2=storeref RPAREN
        {
            result = new SLExpression(tb.subset(t, t2));
        }

    |   NEWELEMSFRESH LPAREN t=storeref RPAREN
        {
            result = new SLExpression(tb.subset(t,
                                                tb.union(convertToOld(t),
                                                         tb.freshLocs(atPres == null ? null : atPres.get(getBaseHeap())))));

        }

    |   (SEQEMPTY
        | (LPAREN (SEQDEF | SEQ) quantifiedvardecls SEMI)
        | (SEQSINGLETON | SEQ) LPAREN
        | SEQSUB LPAREN
        | SEQREVERSE
        | SEQREPLACE
        // | SEQCONTAINS
        | SEQCONCAT
        | SEQGET
        | INDEXOF)
         => result = sequence    
    
    |   LPAREN result=expression RPAREN
;


sequence returns [SLExpression ret = null] throws SLTranslationException
@init {
    ImmutableList<Term> tlist = null;
    KeYJavaType typ;
    Term t, t2;
    Token tk = null;
    Pair<KeYJavaType,ImmutableList<LogicVariable>> declVars = null;
}
@after { ret = result; }
:
        SEQEMPTY
        {
            result = new SLExpression(tb.seqEmpty());
        }
    |   (LPAREN (SEQDEF | SEQ) quantifiedvardecls SEMI) => result=seqdefterm
    |   (SEQSINGLETON | SEQ) LPAREN list=exprList RPAREN
        {
            result = translator.translate("\\seq", SLExpression.class, list, services);
        }

    |   SEQSUB LPAREN e1=expression COMMA e2=expression COMMA e3=expression RPAREN
        {
            result = new SLExpression(tb.seqSub(e1.getTerm(), e2.getTerm(), e3.getTerm()));
        }

    |   SEQREVERSE LPAREN e1=expression RPAREN
        {
            result = new SLExpression(tb.seqReverse(e1.getTerm()));
        }
    |   SEQREPLACE LPAREN e1=expression COMMA e2=expression COMMA e3=expression RPAREN
        {
            // short for "e1[0..e2-1]+e3+e1[e2+1..e1.length-1]"
            final Term minusOne = tb.zTerm("-1");
            final Term ante = tb.seqSub(e1.getTerm(), tb.zero(), tb.add(e2.getTerm(), minusOne));
            final Term insert = tb.seqSingleton(e3.getTerm());
            final Term post = tb.seqSub(e1.getTerm(), tb.add(e2.getTerm(), tb.one()), tb.add(tb.seqLen(e1.getTerm()), minusOne));
            final Term put = tb.seqConcat(ante, tb.seqConcat(insert, post));
            result = new SLExpression(put);
        }
        
    |   (tk2= SEQCONCAT{tk=tk2;} | tk3= SEQGET{tk=tk3;} | tk4= INDEXOF{tk=tk4;})
        LPAREN e1=expression COMMA e2=expression RPAREN
        {
            result = translator.translate(tk.getText(), SLExpression.class, services, e1, e2);
        }
;

mapExpression returns [Token token = null] :
  ( MAP_GET
  | MAP_OVERRIDE
  | MAP_UPDATE
  | MAP_REMOVE
  | IN_DOMAIN
  | DOMAIN_IMPLIES_CREATED
  | MAP_SIZE
  | MAP_SINGLETON
  | IS_FINITE
  )
    { token = input.LT(-2); }
  ;

quantifier returns [Token token = null] :
  ( FORALL
  | EXISTS
  | MIN
  | MAX
  | NUM_OF
  | PRODUCT
  | SUM
  )
    { token = input.LT(-1); }
  ;

specquantifiedexpression returns [SLExpression result = null] throws SLTranslationException
@init {
    p = tb.tt();
}
:
	LPAREN
	q=quantifier
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

	    p = tb.convertToFormula(p);
	    result = translator.translate(q.getText(), SLExpression.class, p, expr.getTerm(), declVars.first, declVars.second, nullable, expr.getType(), services);
	}
	RPAREN
;

oldexpression returns [SLExpression ret=null] throws SLTranslationException
@init {
    KeYJavaType typ;
}
@after {ret = result;}
:
    (
    PRE LPAREN result=expression RPAREN
    |
    OLD LPAREN result=expression (COMMA id=IDENT)? RPAREN
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
    :
        LPAREN
        q=BSUM decls=quantifiedvardecls
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
;
        catch [SLTranslationException ex] {
        resolverManager.popLocalVariablesNamespace();
        throw ex;
        }


seqdefterm returns [SLExpression result=null] throws SLTranslationException
    :
        LPAREN
        q=SEQDEF decls=quantifiedvardecls
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
;
        catch [SLTranslationException ex] {
        resolverManager.popLocalVariablesNamespace();
        throw ex;
        }

quantifiedvardecls returns [Pair<KeYJavaType,ImmutableList<LogicVariable>> result = null]
                   throws SLTranslationException
@init {
    ImmutableList<LogicVariable> vars = ImmutableSLList.<LogicVariable>nil();
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

typespec returns [KeYJavaType ret = null] throws SLTranslationException
@after {ret = t;}
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

type returns [KeYJavaType ret = null] throws SLTranslationException
@after{ ret = t; }
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
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_REAL);
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
	id=IDENT
	{ result += id.getText(); }
	(
	    DOT id1=IDENT
	    { result += "." + id1.getText(); }
	)*
;

quantifiedvariabledeclarator[KeYJavaType t] returns [LogicVariable v = null] throws SLTranslationException
@init {
    KeYJavaType varType = null;
}
:
   id=IDENT (dim=dims)?
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

