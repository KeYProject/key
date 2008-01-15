// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.jml;

import java.util.*;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.Constructor;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.recoderext.ClassInitializeMethodBuilder;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.proof.mgt.JavaModelMethod;
import de.uka.ilkd.key.proof.mgt.ListOfQuantifierPrefixEntry;
import de.uka.ilkd.key.proof.mgt.QuantifierPrefixEntry;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.util.Debug;

/** 
 * A generic jml methodspecification used for encapsulating lightweight
 * and behavioral methodspecifications
 * @deprecated
 */
public class JMLMethodSpec extends JMLSpec implements JMLLemmaMethodSpec, 
						      AssignableSpec{

    public static final String EVERYTHING = "everything";

    protected class ModTermKey{

	private boolean desugar, withInv, allInv;
	
	private int hashValue;
	private Term post;

	public ModTermKey(Term post, boolean desugar, boolean withInv, 
			  boolean allInv){
	    hashValue = 13*post.hashCode() + 3*(desugar ? 1 : 0) +
		5*(withInv ? 1 : 0) + 7*(allInv ? 1 : 0);
	    this.post = post;
	    this.desugar = desugar;
	    this.withInv = withInv;
	    this.allInv = allInv;
	}

	public boolean equals(Object o){
	    if(!(o instanceof ModTermKey)) return false;
	    ModTermKey k = (ModTermKey) o;
	    return k.desugar==desugar && k.withInv==withInv && k.allInv==allInv
		&& post.equals(k.post);
	}

	public int hashCode(){
	    return hashValue;
	}	
    }

    private static final java.util.Comparator comparator = new java.util.Comparator() {
        public int compare(Object o1, Object o2) {
            return (""+o1+o1.hashCode()).compareTo((""+o2+o2.hashCode()).toString());
        }
    };

    
    protected static int excCondCount = 0;
    protected static int exceptionVarCount = 0;
    protected static Term BOOL_FALSE = null;
    protected static Term BOOL_TRUE  = null;
    protected static int logicVarCount = 0;

    protected static Term nullTerm = null;
    protected static int resultVarCount = 0;
    private static final UpdateSimplifier simplifier = new UpdateSimplifier();
    
   
    private static Term addOldQuantifierHelp(Term a, Term t, Term old, 
            boolean useQuantifiers){	
       
        TermBuilder df = TermBuilder.DF;
	if(UsefulTools.occursIn(old, a, false)){
	    if(useQuantifiers){
		LinkedList l = new LinkedList();
		Term t1 = createEqualityTermForOldLV(t, old, l, l, null);
		a = df.imp(t1, a);
                
		if(t.sort() == Sort.FORMULA){
		    old = old.sub(0);
		}
		if(old.op() instanceof ProgramVariable){
		    a = UsefulTools.createQuantifierTermWithPV(
				Op.ALL, old, (LogicVariable) l.getFirst(), a);
		}
	    }else {
		if(t.sort() != Sort.FORMULA && 
		   old.op() instanceof ProgramVariable){
		    a = TermFactory.DEFAULT.createUpdateTerm(old,t,a);
		}else if(t.sort() == Sort.FORMULA && 
			 old.sub(0).op() instanceof ProgramVariable){
		    Term oldVTerm = old.sub(0);
		    LogicVariable oldlv = 
			new LogicVariable(
			      new Name(oldVTerm.op().name().toString()+
				       "_lv"),
			      BOOL_FALSE.sort());		   
		    
                    final Term t1 = df.equals(df.var(oldlv), BOOL_TRUE);
		    t = df.equiv(t, t1); 		  
		    a = UsefulTools.createQuantifierTermWithPV(
					  Op.ALL, oldVTerm, oldlv, 
                                          df.imp(t, a));
		}else{
		    t = createEqualityTermForOldLV(t, old, null, null, null);
		    a = df.imp(t, a);
		}
	    }
	}
	return a;
    }
    /** Applies the transformation tau_update to <code>a</code> iff 
     * <code>useQuantifiers == false</code> or tau_old otherwise.
     */
    public static Term addOldQuantifiers(Term a, Map term2old, 
					 boolean useQuantifiers,
					 Namespace params){
	if(a==null) return a;
	final TreeMap param2old = new TreeMap(comparator);
	final Set sortedKeys;
	if (term2old instanceof SortedMap) {
            sortedKeys = term2old.keySet();
        } else {
            sortedKeys = new TreeSet(comparator);
            sortedKeys.addAll(term2old.keySet());
	}
	final Iterator it = sortedKeys.iterator();
	while(it.hasNext()){
	    Term t = (Term) it.next();
	    Term old = (Term) term2old.get(t);
	    if(params != null && t!=null &&
	       params.lookup(t.op().name()) != null && 
	       params.lookup(t.op().name()).equals(t.op())){
		param2old.put(t, old);
	    }else{
		a = addOldQuantifierHelp(a, t, old, useQuantifiers);
	    }
	}
	// it is necessary that old-variables associated with parameters are
	// updated first because parameters are always implicitely refered to 
	// in their prestate, which 
	// can lead to nested old-expressions.
	// example: let x be a parameter: 
	// transforming <P>(... \old(x[i]) ...) to 
	// {old1:=old2[i]}{old2:=x}<P>(... old1 ...) is obviously wrong
	// since x has not yet been assigned to old2 when the update
	// {old1:=old2[i]} is applied.
	// the correct transformation would be:
	// {old2:=x}{old1:=old2[i]}<P>(... old1 ...)
	if(params != null && !param2old.isEmpty()){
	    a = addOldQuantifiers(a, param2old, useQuantifiers, null);
	}
	return a;
    }
    

    protected static Term createEqualityTermForOldLV(
	Term t, Term old, LinkedList l, LinkedList oldFS, Map lv2old){
	TermFactory tf0 = TermFactory.DEFAULT;
	Term lvTerm = null; 
	Term lvEq = null;
	LogicVariable oldlv=null; 
	if(!(old.op() instanceof ProgramVariable) || 
	   old.sort() == Sort.FORMULA && 
	   !(old.sub(0).op() instanceof ProgramVariable)){
	    Term oldFTerm = (t.sort() == Sort.FORMULA ?
			     old.sub(0) : old);
	    t = tf0.createEqualityTerm(old, t);
	    if(oldFS!=null){
		if(oldFTerm.op() instanceof ArrayOp){
		    oldFS.add(oldFTerm.sub(0).op());
		}else{
		    oldFS.add(oldFTerm.op());
		}
	    }
	    for(int i = (oldFTerm.op() instanceof ArrayOp)? 1 : 0; 
		i<oldFTerm.arity(); i++){
		if(oldFTerm.sub(i).op() instanceof ProgramVariable){
		    LogicVariable arglv = 
			new LogicVariable(
			    new Name(oldFTerm.sub(i).op().name().
				     toString()+
				     "_lv"),
			    oldFTerm.sub(i).sort());
		    t = UsefulTools.
			createQuantifierTermWithPV(Op.ALL, oldFTerm.sub(i), 
						   arglv, t);
		}else{
		    t = tf0.createQuantifierTerm(
			Op.ALL, (LogicVariable) oldFTerm.sub(i).op(), t);
		}
	    }
	    return t;
	}else{
	    if(t.sort() != Sort.FORMULA){
		oldlv = 
		    new LogicVariable(new Name("y"+(logicVarCount++)),
				      t.sort());
		l.add(oldlv);
		lvEq = lvTerm = tf0.createVariableTerm(oldlv);
	    }else{
		oldlv = new LogicVariable(
		    new Name("y"+(logicVarCount++)),
		    BOOL_FALSE.sort());
		l.add(oldlv);
		lvTerm = tf0.createVariableTerm(oldlv);
		lvEq = tf0.createEqualityTerm(lvTerm,BOOL_TRUE);
		old = old.sub(0);
	    }
	    Term t1 = tf0.createEqualityTerm(lvEq, t);
	    if(lv2old != null) lv2old.put(lvTerm, old);
	    return t1;
	}
    }

    // contains an assignable keyword (like nothing, everithing, ...), 
    // if one occurd in the specification.
    protected String assignableMode = null;
    protected SetOfLocationDescriptor assignableVariables 
            = SetAsListOfLocationDescriptor.EMPTY_SET;
    private CatchAllStatement catchAllStmt;
    //caches the classdeclaration from cSpec
    protected TypeDeclaration cd;
    protected JMLClassSpec cSpec;
    protected Term diverges;
    protected KeYJavaType exc;
    protected ProgramVariable excVar;
    // counter for distinguishing different specs of one method.
    protected int id;
    //contains the self-variable used in an inherited methodspec.
    protected ReferencePrefix inheritedPrefix = null;
    protected String inhFrom = "";
    private String javaPath;
    protected JavaInfo ji;
    protected TreeMap lv2old;
    private TreeMap lv2const;
    protected StatementBlock mBS = null;
    protected LinkedHashMap modalityTermForEnsuresCache = new LinkedHashMap();
    protected NamespaceSet nss;
    private ListOfQuantifierPrefixEntry oldLVs = null;
    private ListOfOperator oldFuncSymbols;
    protected Namespace params;
    private Term pi1 = null;
    protected ProgramMethod pm;
    private Term post; 
    private Term pre;
    protected ProgramVariable resultVar = null;
    /**
     * Specification variables (see JML Reference
     * Manual, section about Specification Variable Declarations)
     */
    private ListOfNamed specVars = SLListOfNamed.EMPTY_LIST;
    
    public Map getLv2Const() {
	if(lv2const == null) {
	    lv2const = new TreeMap(comparator);
	}
	return lv2const;
    }

    
    protected ProgramVariable self;

    protected Services services;


    protected SetOfSignals signals = SetAsListOfSignals.EMPTY_SET;

    //flag which is set to false iff static initialisation features should be suppressed
    protected boolean staticInit=false;

    protected TermBuilder tb;

    protected LinkedHashMap term2old;

    protected JMLMethodSpec(){}

    public JMLMethodSpec(ProgramMethod pm, 
			 Services services, Namespace params, 
			 LinkedHashMap term2old, JMLClassSpec cSpec, 
			 NamespaceSet nss, String javaPath){
        this.pm = pm;
	this.progVarNS = new Namespace(cSpec.getProgramVariableNS());
	this.funcNS    = new Namespace(cSpec.getFunctionNS());
	this.cd  = cSpec.getClassDeclaration();
	this.nss = nss;
	this.ji  = services.getJavaInfo();
	this.services = services;
	this.javaPath = javaPath;
        
	if(nullTerm == null){
	    nullTerm = NULL(services);
	}
	if(BOOL_TRUE == null){
	    BOOL_TRUE = TRUE(services);
	}
	if(BOOL_FALSE == null){
	    BOOL_FALSE = FALSE(services);
	}
	pre = post = tt();

	if(!pm.isStatic()){
	    createSelfAndAddImplicitPreconditions(pm, services, cSpec);
	}        
	if(staticInit && !pm.getName().equals
	        (ClassInitializeMethodBuilder.CLASS_INITIALIZE_IDENTIFIER)){
	    addImplicitPreconditionsForStaticMethods(services);
            
	}

	services.getImplementation2SpecMap().addMethodSpec(this);
	diverges = ff();
	this.params = params;
	this.term2old = term2old;
	this.cSpec = cSpec;
	exc = services.getJavaInfo().getTypeByClassName("java.lang.Exception");
	excVar = new LocationVariable(new ProgramElementName(
			       "_exc"+(exceptionVarCount++)), exc);
	//	progVarNS.add(excVar);
	resultVar = makeResultVar();
    }
    
    public void addAssignable(SetOfLocationDescriptor locations){	
        assignableVariables = assignableVariables.union(locations);
    }
    
    public SetOfLocationDescriptor getAssignable() {
        if (EVERYTHING.equals(getAssignableMode()) &&
                assignableVariables.size() == 0) {
            return SetAsListOfLocationDescriptor.EMPTY_SET.
               add(EverythingLocationDescriptor.INSTANCE);                        
        }
        return assignableVariables;
    }

    public void addSignals(KeYJavaType exc, ProgramVariable v, Term cond){
	if(v != null){
	    getProgramVariableNS().add(v);
	}
	signals = signals.add(new Signals(exc, v, cond));
    }

    protected JavaBlock catchAllJB(boolean desugar){
	JavaBlock catchAllJB;
	if(catchAllStmt == null){
	    ParameterDeclaration param = 
		new ParameterDeclaration(new Modifier[0], new TypeRef(exc),
					 new VariableSpecification(excVar), 
					 false);
	    catchAllStmt = new CatchAllStatement(makeMBS(), param);
	}
	if(desugar){
	    catchAllJB = 
		JavaBlock.createJavaBlock(
		    (StatementBlock) catchAllStmt.desugar());
	}else{
	    catchAllJB = JavaBlock.createJavaBlock(new StatementBlock(
						       catchAllStmt));
	}
	return catchAllJB;
    }

    public void clearModalityTermForEnsuresCache(){
	modalityTermForEnsuresCache.clear();
    }

    /**
     * This is used for modelling specification inheritance for overwritten
     * methods.
     */
    public JMLMethodSpec cloneFor(ProgramMethod pm, JMLClassSpec cSpec){
	if(!isCloneableFor(pm)) return null;
	JMLMethodSpec cloned = new JMLMethodSpec();
	return cloneForHelper(cloned, pm, cSpec);
    }

    public JMLMethodSpec copy(){
	JMLMethodSpec copy = 
	    new JMLMethodSpec(pm, services, params, 
			      term2old, cSpec, nss, javaPath);
	return copyHelper(copy);
    }
    
    
    protected String toStringHelper(String s) {
	return isValid() ?
	    inhFrom+s+" for method "+pm.getName()+
	    "\nin context "+cd.getName()+
	    "\nrequires: "+
	    (pre==null ? "true" : 
	        ProofSaver.printTerm(pre, services, true).toString())
	    :
	    "Invalid method spec due to unsupported expression: "+
	    nsEx.expression();
    }

    public String toString(){
	return toStringHelper("behavior speccase "+id);
    } 

    /**
     * copys several fields to the incomplete copy <code>copy</copy> of this.
     */
    protected JMLMethodSpec copyHelper(JMLMethodSpec copy){
	copy.services = services;
	copy.progVarNS = progVarNS.copy();
	copy.funcNS = funcNS.copy();
	copy.tb = tb;
	copy.nss = nss;
	copy.params = params;
	copy.pre = pre;
	copy.post = post;
	copy.resultVar = resultVar;
	copy.assignableMode = getAssignableMode();
	copy.diverges = diverges;
	copy.term2old = (LinkedHashMap) term2old.clone();
	copy.assignableVariables = assignableVariables;
	copy.signals = signals;
	copy.excVar = excVar;
	copy.exc = exc;
	copy.specVars = specVars;
	copy.nsEx = nsEx;
	copy.ji = services.getJavaInfo();
	return copy;
    }

    protected JMLMethodSpec cloneForHelper(JMLMethodSpec clone, 
					   ProgramMethod pm, 
					   JMLClassSpec cSpec){
	clone = copyHelper(clone);
	clone.id = id;
	clone.inhFrom = inhFrom.equals("") ?
	    "inherited from "+cd.getName()+" " : inhFrom;
	clone.cSpec = cSpec;
	//set new prefix
	if(!pm.isStatic()){
	    if(inheritedPrefix == null){
		clone.inheritedPrefix = getPrefix();
	    }else{
		clone.inheritedPrefix = inheritedPrefix; 
	    }
	    clone.self = (ProgramVariable) cSpec.getInstancePrefix();
	}
	clone.cd = cSpec.getClassDeclaration();
	KeYJavaType returnType;
	if(pm.getTypeReference() == null){
	    returnType = ji.getKeYJavaType("void");
	}else{
	    returnType = pm.getTypeReference().getKeYJavaType();
	}

	//replace the old arguments by the new ones
	Namespace newPNS = UsefulTools.buildParamNamespace(pm.getMethodDeclaration());
	Namespace oldPNS = clone.params;
	ArrayOfParameterDeclaration oldParams = this.pm.getParameters();
	ArrayOfParameterDeclaration newParams = pm.getParameters();
	clone.progVarNS.add(oldPNS.allElements());
	clone.params = newPNS;
	clone.post = updateParameters(oldParams, newParams, clone.post);
	clone.pre = updateParameters(oldParams, newParams, clone.pre);
        clone.pm = 
            new ProgramMethod(pm.getMethodDeclaration(), 
                        ji.getKeYJavaType(cSpec.getClassDeclaration()), 
                              returnType, PositionInfo.UNDEFINED);        
	SetOfSignals si = SetAsListOfSignals.EMPTY_SET;
	IteratorOfSignals it = clone.signals.iterator();
	while(it.hasNext()){
	    Signals s = it.next();
	    si = si.add(new Signals(s.type(), s.variable(), 
				    s.condition() == null? null :
				    clone.updatePrefix(
					 updateParameters(oldParams, newParams,
							  s.condition()))));
	}
	clone.signals = si;
	Iterator kit = term2old.keySet().iterator();
	clone.term2old = new LinkedHashMap();
	while(kit.hasNext()){
	    Term t = (Term) kit.next();
	    clone.term2old.put(clone.updatePrefix(
				    updateParameters(oldParams, newParams, t)),
				    term2old.get(t));
	}

	clone.progVarNS.add(cSpec.getProgramVariableNS());
	clone.funcNS.add(cSpec.getFunctionNS());

	if(staticInit && !pm.getName().equals
	        (ClassInitializeMethodBuilder.CLASS_INITIALIZE_IDENTIFIER) &&
	    !(cSpec.getClassDeclaration() instanceof InterfaceDeclaration)){
	    ProgramVariable ci = 
	        services.getJavaInfo().getAttribute
	        (ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, 
	                ji.getKeYJavaType(cSpec.getClassDeclaration()));
	    if(ci != null){
		clone.addPre(equals(tf.createVariableTerm(ci), BOOL_TRUE));
	    }
	}
	clone.updateAssignableLocations();
        clone.javaPath = javaPath;
	return clone;
    }

    /**
     * @param t1 the precondition.
     * @param jb the JavaBlock used in the modality.
     */
    protected Term createDiverges(){
	if(diverges != null && !ff().equals(diverges)){
	    final Term div = tf.createDiamondTerm(catchAllJB(true), tt());
	    final Term divPre = updatePrefix(not(diverges));
	    return imp(divPre, div);
	}
	return tt();
    }

    /** Creates a DL formula from this method specification:
     * ((pre & inv) -> [{methodbody}]post) & ((pre & inv & !diverges) -> <{methodbody}>post)
     * (This is the DL formula that is needed for an "ensured postcondition 
     * proofobligation")
     * @param withInvariant: iff true the invariant of the containing type
     * is added to the postcondition which is needed for JMLPostAndInvPOs 
     * created by JMLMethodContracts.
     * @param allInvariants: iff true all existing invariants for every 
     * existing type are added to the precondition (and postcondition if 
     * withInvariant is also true).
     */
    public Term createDLFormula(boolean withPostInvariant, 
				boolean allInvariants){
	Term result,t1,t2;
	result = t2 = null;
	t1 = getPre();
	if(allInvariants && !services.getImplementation2SpecMap().
	   getModifiers(pm).contains("helper")){
	    Term ai = UsefulTools.allInvariants(
		services.getImplementation2SpecMap());
	    t1 = UsefulTools.makeConjunction(t1, ai);
	}else{
	    t1 = cSpec.addClassSpec2Pre(t1, pm, cSpec);
	}
	t2 = getPost();
	if(t2 == null){
	    result= createModalityTermForEnsures(tt(), true, 
						 withPostInvariant,
						 allInvariants);
	}else{
	    result= createModalityTermForEnsures(t2, true,
						 withPostInvariant,
						 allInvariants);
	}
	if(diverges != null && !ff().equals(diverges)){
	    result = and(result, createDiverges()); 
	}
	if(t1 != null){
	    result = imp(t1, result);
	}
	result = addOldQuantifiers(result, term2old, false, params);
	
        if(cSpec!=null){
	    result = addOldQuantifiers(result, cSpec.getTerm2Old(), false, 
				       null);
	}
	
        if(!pm.isStatic()){
	    result = updatePrefix(result);
	}
	
        result = UsefulTools.addRepresents(result, services, 
					   (ProgramVariable) 
					   cSpec.getInstancePrefix());
/*	if(UsefulTools.purityCheck(result, 
				   services.getImplementation2SpecMap())
	    != null){
	    throw new RuntimeException("Nonpure method "+ 
				       UsefulTools.purityCheck(result, 
					 services.getImplementation2SpecMap())+
				       " used in the "+
				       "specification for method "+
				       pm.getName());
				       }*/
	if(!pm.isStatic()){
	    result = UsefulTools.quantifySelf(result, pm.getMethodDeclaration(), 
	    		                          (ProgramVariable)getPrefix());
	}
	result = bindSpecVars(result);
	return imp(func(services.getJavaInfo().getInReachableState()), 
                UsefulTools.quantifyProgramVariables(result, 
			    params.allElements().iterator(), Op.ALL, services));
    }

    public Term bindSpecVars(Term t){
	IteratorOfNamed it= specVars.iterator();
	while(it.hasNext()){
	    LogicVariable lv = (LogicVariable) it.next();
	    t = tf.createQuantifierTerm(Op.ALL, lv, t);
	}
	return t;
    }

    public void addPre(Term t){
	if(t != null){
	    pre = and(pre, t);
	}
    }

    public void addPost(Term t){
	if(t != null){
	    post = and(post, t);
	}
    }

    public void setSpecVars(ListOfNamed svs){
	specVars = svs;
    }

    public ListOfNamed getSpecVars(){
	return specVars;
    }

    public void addDiverges(Term t){
	if(t != null){
	    diverges = or(diverges, t);
	}
    }

    private Term createdOrNull(ProgramVariable var) {
        final Term tVar = var(var);
	return or(equals(tVar, NULL(services)), 
                  UsefulTools.isCreated(tVar, services));
    }

    protected Term createModalityTermForEnsures(Term post, boolean desugar,
						boolean withInv, 
						boolean allInv){
	ModTermKey key = new ModTermKey(post, desugar, withInv, allInv);
	Term c = (Term) modalityTermForEnsuresCache.get(key);
	if(c != null){
	    return c;
	}
        Term excPost = tt();
        Term excVarTerm = var(excVar);
	post = imp(equals(excVarTerm, nullTerm), post);	
        final IteratorOfSignals it = signals.iterator();
	while(it.hasNext()){
	    final Signals sig = it.next();	    
	    final SortDefiningSymbols s = (SortDefiningSymbols)(sig.type().getSort());
	    final InstanceofSymbol func
		= (InstanceofSymbol)s.lookupSymbol(InstanceofSymbol.NAME);	  
	    
            Term post1 = 
                imp(equals(func(func, excVarTerm), BOOL_TRUE), sig.condition());
	   
            if(sig.variable() != null){
		post1 = tf.createUpdateTerm(var(sig.variable()), excVarTerm, post1);
	    }
            excPost = and(excPost, post1);
	}
        
	final JavaBlock jb = catchAllJB(desugar);
	if(excPost != null){
	    excPost = imp ( not ( equals (excVarTerm, nullTerm) ), excPost);
	    post    = and(post, excPost);
	}
	if(withInv && !services.getImplementation2SpecMap().
	   getModifiers(pm).contains("helper")){
	    post = cSpec.addClassSpec2Post(post, true, !allInv, pm, cSpec); 
	    if(allInv){
		Term ai = UsefulTools.allInvariants(
		    services.getImplementation2SpecMap());
		if(ai != null){
		    post = and(ai, post);
		}
	    }
	}
	post = updatePrefix(post);
	post = UsefulTools.addRepresents(post, services, 
					 (ProgramVariable) 
					 cSpec.getInstancePrefix());
	if(diverges == null || ff().equals(diverges)){
	    c = dia(jb, post);
	}else{
	    c = box(jb, post);
	}
	modalityTermForEnsuresCache.put(key, c);
	return c;
    }

    /**
     * creates and sets the self (this) prefix variable. In addition implicit
     * method preconditions are added. Implicit means the JML semantics requires them to
     * be fulfilled and therefore the specifier does not need to state them explicitly.
     * Such invariants are, e.g. 
     *    <ul>
     *       <li> "this" (self) is not null and it is a created object</li>
     *    </ul>     
     */
    private void createSelfAndAddImplicitPreconditions(ProgramMethod pm,
            Services services, JMLClassSpec cSpec) {
        self = (ProgramVariable)cSpec.getInstancePrefix();
        Term t_self = var(self);
        //adds self!=null && self.<created> == true or 
        //self.<classInitialized> == true to the precondition
        if(!(pm.getMethodDeclaration() instanceof Constructor)){
            addPre(not(equals(t_self, nullTerm)));
            addPre(UsefulTools.isCreated(t_self, services));
        }
    }

    /**
     * add implicit preconditions for static methods, like: 
     * class is initialized etc.
     */
    private void addImplicitPreconditionsForStaticMethods(Services services) {
        final ProgramVariable ci = ji.getAttribute
                (ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, 
                        services.getJavaInfo().getKeYJavaType(cd));
            addPre(equals(var(ci), BOOL_TRUE));
    }
    
    public boolean containsQuantifiedAssignableLocation(){
        IteratorOfLocationDescriptor it = assignableVariables.iterator();
        while(it.hasNext()){
            LocationDescriptor loc = it.next();
            if(containsQuantifiedLocationHelp(loc)){
                return true;
            }
        }
        return false;
    }

    private boolean containsQuantifiedLocationHelp(LocationDescriptor loc){
        if(loc instanceof BasicLocationDescriptor) {
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
            return !bloc.getFormula().equals(tt()) 
                   || bloc.getLocTerm().freeVars().size() > 0;
        }
        return false;
    } 

  

    public String getAssignableMode(){
	if(services.getImplementation2SpecMap().getModifiers(pm).
	   contains("pure") && 
	   assignableVariables == SetAsListOfLocationDescriptor.EMPTY_SET){
	    return "nothing";
	}
	if(assignableVariables == SetAsListOfLocationDescriptor.EMPTY_SET &&
	    assignableMode == null){
	    return EVERYTHING;
	}
	// an inconsistent case
	if(assignableVariables != SetAsListOfLocationDescriptor.EMPTY_SET &&
	   "nothing".equals(assignableMode)){
	    return null;
	}
	return assignableMode;
    }

    public CatchAllStatement getCatchAllStatement() {
        return catchAllStmt;
    }
    
    public TypeDeclaration getClassDeclaration(){
        return cd;
    }    
    
    public Term getCompletePost(boolean withClassSpec, boolean allInv){
        Term result;
        if(oldLVs == null){
            getPi1();
        }
        if(getPost() == null){
            result =
                createModalityTermForEnsures(tt(), false, withClassSpec,
                                             allInv);
        }else{
            result =
                createModalityTermForEnsures(getPost(), false, withClassSpec,
                                             allInv);
        }
        result = result.sub(0);
        result = addOldQuantifiers(result, lv2old, false, params);
        if(!(pm.getMethodDeclaration() instanceof Constructor)){
            result = updatePrefix(result);
        }
        if (resultVar != null &&
            resultVar.sort() instanceof ObjectSort) {
            result = and(result, createdOrNull(resultVar));
        }
        return result;
    }
    
    public Term getCompletePostFunctional(boolean withClassSpec, boolean allInv){
        Term t = getCompletePost(withClassSpec, allInv);
        return replaceFreeVarsWithConsts(t);
    }

    /** 
     * returns the precondition + represents for model fields
     * (+ invariants iff withClassSpec = true, + the negation of the diverges
     * clause in order to retrieve a precondition under which the method must 
     * terminate).
     */
    public Term getCompletePre(boolean withClassSpec, boolean allInv,
			       boolean terminationCase){
	Term t = getPre();
	if(withClassSpec){
	    if(allInv && !services.getImplementation2SpecMap().
	       getModifiers(pm).contains("helper")){
		Term ai = UsefulTools.allInvariants(
		    services.getImplementation2SpecMap());
		t = UsefulTools.makeConjunction(t, ai);
	    }else{
		t = cSpec.addClassSpec2Pre(t, pm, cSpec); 
	    }
	}
	if(terminationCase && diverges != null && !ff().equals(diverges)){
	    Term divPre = not (diverges); 
	    divPre = updatePrefix(divPre);
	    t = and(divPre, t);
	}
	t = UsefulTools.addRepresents(t, services, 
				      (ProgramVariable) 
				      cSpec.getInstancePrefix());
	t = updatePrefix(t);
	return t==null? tt() : t; 
    } 

    /**
     * returns the ProgramVariable that is used for expressing the excetional
     * behavior of a method. 
     */
    public ProgramVariable getExceptionVariable(){
	return excVar;
    }

    public ReferencePrefix getInheritedPrefix(){
	return inheritedPrefix;
    }

    public String getJavaPath() {
    	return javaPath;
    }

    public MethodDeclaration getMethodDeclaration(){
	return pm.getMethodDeclaration();
    }

    public JavaModelMethod getModelMethod() {
    	return new JavaModelMethod(getProgramMethod(), javaPath, services);
    }

    public NamespaceSet getNamespaces() {
        return nss;
    }
    
    public ProgramVariable getParameterAt(int i) {
        return (ProgramVariable) pm.getParameters().getParameterDeclaration(i)
                                .getVariableSpecification().getProgramVariable();
    }
    
    public ListOfQuantifierPrefixEntry getOldLVs(){
	if(oldLVs == null){
	    getPi1();
	}
	return oldLVs;
    }

    public ListOfOperator getOldFuncSymbols(){
	if(oldFuncSymbols == null){
	    getPi1();
	}
	return oldFuncSymbols;	
    }

    public Term getPi1(){
	if(pi1 == null){
	    lv2old = new TreeMap(comparator);
	    LinkedList l = new LinkedList();
	    LinkedList oldFS = new LinkedList();
	    pi1 = getPi1Helper(tt(), l, oldFS, term2old);
	    pi1 = getPi1Helper(pi1, l, oldFS, cSpec.getTerm2Old());
	    pi1 = UsefulTools.addRepresents(pi1, services, 
				      (ProgramVariable) 
					    cSpec.getInstancePrefix());
	    oldLVs = QuantifierPrefixEntry.toUniversalList ( l.iterator () );
	    oldFuncSymbols = toOpList(oldFS);
	}
	return pi1;
    }
   
    private ListOfOperator toOpList(List l){
	ListOfOperator result = SLListOfOperator.EMPTY_LIST;
	Iterator it = l.iterator();
	while(it.hasNext()){
	    result = result.append((Operator) it.next());
	}
	return result;
    }
    
    public Term getPi1Functional() {
        return replaceFreeVarsWithConsts(getPi1());
    }

    private Term getPi1Helper(Term pi1, LinkedList l, 
			      LinkedList oldFS, HashMap map){
	Set sortedKeyset = new TreeSet(comparator);
        sortedKeyset.addAll(map.keySet());
        final Iterator it = sortedKeyset.iterator();
	Term postAndInvTerm = 
	    createModalityTermForEnsures(getPost() == null?
					 tt() : getPost(),
					 false, true, false);
	while(it.hasNext()){
	    Term t = (Term) it.next();
	    Term old = (Term) map.get(t);
	    if(UsefulTools.occursIn(old, postAndInvTerm, false)){
		Term t1 = createEqualityTermForOldLV(t, old, l, oldFS, lv2old);
		if(pi1 == tt()){
		    pi1 = t1;
		}else{
		    pi1 = and(pi1, t1);
		}
	    }
	}
	return pi1;
    }


    /**
     * returns the locally declared postcondition
     */
    public Term getPost(){
	return post;
    }

    /**
     * returns the locally declared precondition
     */
    public Term getPre(){
	return pre;
    }

    public ReferencePrefix getPrefix(){
	if(pm != null && pm.isStatic()){
	    return cSpec.getStaticPrefix();
	}else{
	    return cSpec.getInstancePrefix();
	}
    }

    public ProgramMethod getProgramMethod(){
	return pm;
    }

    public ProgramElement getProofStatement(){
	return createModalityTermForEnsures(post == null ? tt() : post, 
					    false, false, false).
	    javaBlock().program();
    }

    public ProgramVariable getResultVar(){
	if(resultVar == null){
	    resultVar = makeResultVar();
	}
	return resultVar;
    }

    public ProgramVariable getSelf() {
        return self;
    }

    public Services getServices() {
        return services;
    }
    
    public SetOfSignals getSignals(){
	return signals;
    }

    public LinkedHashMap getTerm2Old(){
	return term2old;
    }

    public int id(){
	return id;
    }


    /**
     * Checks if name, signature, accessibility and so on are equal for 
     * this.pm and pm. If this.pm and pm occur on the same branch in the
     * class hierarchy must be checked somewhere else!
     */
    public boolean isCloneableFor(ProgramMethod method){
	if(!method.getName().equals(this.pm.getName())){
	    return false;
	}
	
        final TypeReference methTypeRef = method.getTypeReference();
        if((methTypeRef != null && 
	    !methTypeRef.equals(this.pm.getTypeReference())) ||
	   (methTypeRef == null && this.pm.getTypeReference() != null)){
	    return false;
	}
	
        final Throws methThrown = method.getThrown();
        if((methThrown != null && 
	    !methThrown.equals(this.pm.getThrown())) ||
	    (methThrown == null && this.pm.getThrown() != null)){
	    return false;
	}
	
        if(method.getParameterDeclarationCount() != 
	       this.pm.getParameterDeclarationCount()){
	    return false;
	}
	for(int i = 0; i<method.getParameterDeclarationCount(); i++){
	    if(!method.getParameterType(i).equals(this.pm.getParameterType(i))){
		return false;
	    }
	}
	final int methModSize = method.getModifiers().size();
        final int thisPMethModSize = this.pm.getModifiers().size();
        if(methModSize != thisPMethModSize +
	   ((cd instanceof InterfaceDeclaration) ? 1 : 0) - 
	   (pm.isAbstract() ? 1 : 0)){
	    return false;
	}
	
	for(int i = 0; i<methModSize; i++){
	    boolean equal = false;
	    final Modifier modifier = method.getModifiers().getModifier(i);
	    
	    if (!((cd instanceof InterfaceDeclaration) && 
	            modifier instanceof Public)) {
	        
	        for(int j = 0; j<thisPMethModSize; j++){
	            if(modifier.equals(this.pm.getModifiers().getModifier(j))){
	                equal = true;
	                break;
	            }
	        }
	        if(!equal) return false;
	    }
	}
	return true;
    }

    public StatementBlock makeMBS(){
	if(mBS == null){
	    ArrayOfParameterDeclaration aopd = pm.getParameters();
	    Expression[] aop = new Expression[pm.getParameters().size()]; 
	    for(int i=0; i<aopd.size(); i++){
		aop[i] = (ProgramVariable) aopd.
		    getParameterDeclaration(i).
		    getVariableSpecification().getProgramVariable();
	    }
	    if(!(pm.getMethodDeclaration() instanceof Constructor)){
		MethodBodyStatement mb = new MethodBodyStatement(
		    pm,
		    pm.isStatic() ? null : getPrefix(),
		    getResultVar(),
		    new ArrayOfExpression(aop));
		mBS = new StatementBlock(mb);
	    }else{
		New n = new New(aop, (TypeReference) cSpec.getStaticPrefix(), null);
		MethodFrame fakeFrame = new MethodFrame
		    (null, 
		     new ExecutionContext((TypeReference) cSpec.getStaticPrefix(), null), 
		     new StatementBlock(new CopyAssignment((ProgramVariable) getPrefix(), n)));
		mBS = new StatementBlock(fakeFrame);
	    }
	}
	return mBS;
    }
    
/*    public StatementBlock buildOuterClassesContext(StatementBlock mbs){
        System.out.println("JMLMethodSpec: class: "+cSpec.getClassDeclaration().getFullName());
        System.out.println("JMLMethodSpec: ji.getKJT(class fullname): "+ji.getKeYJavaType(cSpec.getClassDeclaration().getFullName()));
        System.out.println("JMLMethodSpec: parent class: "+cSpec.getClassDeclaration().getParentClass());
        ExecutionContext ec = buildExecutionContext(cSpec.getClassDeclaration().getFullName());
        System.out.println("JMLMethodSpec: ec: "+ec);
        StatementBlock sb = mbs;
        while(ec!=null){
            sb = new StatementBlock(new MethodFrame(null, ec, sb));
            ec = (ExecutionContext) ec.getParent();
        }
        return sb;
    }
    
    private ExecutionContext buildExecutionContext(String fullName){
        int end = fullName.lastIndexOf(".");
        if(end==-1 || ji.getKeYJavaType(fullName.substring(0, end))==null){
            return null;
        }
        KeYJavaType outer = ji.getKeYJavaType(fullName.substring(0, end));
        TypeReference tr = new TypeRef(outer);
        ReferencePrefix rp = services.getImplementation2SpecMap().getSpecForClass(outer).getInstancePrefix();
        return new ExecutionContext(tr, rp, buildExecutionContext(fullName.substring(0, end)));
    }*/

    private ProgramVariable makeResultVar(){
	if(pm.getTypeReference()==null){
	    return null;
	}
	ProgramVariable v = 
	    new LocationVariable(new ProgramElementName("_jmlresult"+
						       (resultVarCount++)),
				pm.getTypeReference().getKeYJavaType());
	progVarNS.add(v);
	return v;
    }

    public Term replaceFreeVarsWithConsts(Term t) {
        SetOfQuantifiableVariable vars = t.freeVars();
        if (vars.size()==0) {
            return t;
        }
        IteratorOfQuantifiableVariable it = vars.iterator();
        while (it.hasNext()) {
            QuantifiableVariable qv = it.next();
            if (lv2const == null) {
                lv2const = new TreeMap(comparator);
            }
            if (!lv2const.containsKey(qv)) {
                lv2const.put(qv, new RigidFunction(qv.name(), qv.sort(), new Sort[0]));
                
            }
        }
        Iterator entriesIt = lv2const.entrySet().iterator();
        while (entriesIt.hasNext()) {
            Map.Entry e = (Map.Entry) entriesIt.next();
            ClashFreeSubst subst
                = new ClashFreeSubst((QuantifiableVariable)e.getKey(),
                        func((RigidFunction)e.getValue()));
            t = subst.apply(t);
        }
        return t;
    }
    
    public Collection introducedConstants() {
        return new HashSet(getLv2Const().values());
    }
    
    public SetOfLocationDescriptor replaceModelFieldsInAssignable(){
        return replaceModelFieldsInAssignable(cSpec);
    }

    public SetOfLocationDescriptor replaceModelFieldsInAssignable(
                                                            JMLClassSpec cs){
        if(assignableVariables == SetAsListOfLocationDescriptor.EMPTY_SET){
            if("nothing".equals(getAssignableMode())){ 
                return assignableVariables;
            }else{
                return null;
            }
        }
        SetOfLocationDescriptor result = assignableVariables;
        /*      IteratorOfTerm it = assignableVariables.iterator();
        while(it.hasNext()){
            Term varTerm = it.next();
            System.out.println("replaceModelFieldsInAssignable3: "+varTerm);
            Term rep = (Term) cs.getRepresents().get(varTerm);
            System.out.println("replaceModelFieldsInAssignable4: "+rep);
            if(rep != null){
                System.out.println("replaceModelFieldsInAssignable5");
                result = result.remove(varTerm).add(rep);
            }
            }*/
        return result;
    }
    
    /**
     * Replaces occurences of the inherited prefix and the inherited parameters
     * in <code>t</code> with the current prefix and the current parameters,
     * respectively.
     */
    private Term replaceSelf(Term t){
	if(t.op() == inheritedPrefix){
	    return var(self);
	}else if(t.op() instanceof ProgramVariable){
	    if(params.lookup(t.op().name()) != null){
		return var((ProgramVariable)params.lookup(t.op().name()));
	    }
	    return t;
	}else{
	    Term[] subs = new Term[t.arity()];
	    for(int i = 0; i<t.arity(); i++){
		subs[i] = replaceSelf(t.sub(i));
	    }
	    return tf.createTerm(t.op(), subs,(ArrayOfQuantifiableVariable) null, 
				 null);
	}
    }

    public void setAssignableMode(String s){
	assignableMode = s;
    }

    public void setId(int id){
	this.id = id;
    }

    /**
     * returns true if this specification demands termination of the method,
     * which means in this case that terminating by throwing an exception
     * is also considered to be a termination.
     */
    public boolean terminates(){
	return diverges == null || diverges.equals(ff());
    }

    private void updateAssignableLocations(){
        if(!(pm.isStatic() || 
                pm.getMethodDeclaration() instanceof Constructor)){
            IteratorOfLocationDescriptor it = assignableVariables.iterator();
            assignableVariables = SetAsListOfLocationDescriptor.EMPTY_SET;
            while(it.hasNext()){
                LocationDescriptor loc = it.next();
                LocationDescriptor newLoc;
                if(loc instanceof BasicLocationDescriptor) {
                    BasicLocationDescriptor bloc = (BasicLocationDescriptor)loc;
                    newLoc = new BasicLocationDescriptor(
                            replaceSelf(bloc.getFormula()), 
                            replaceSelf(bloc.getLocTerm()));

                } else {
                    Debug.assertTrue(
                            loc instanceof EverythingLocationDescriptor);
                    newLoc = loc;
                }
                assignableVariables = assignableVariables.add(newLoc);
            }
        }      
    }


    protected Term updateParameters(ArrayOfParameterDeclaration oldParams, 
				    ArrayOfParameterDeclaration newParams, 
				    Term target){
	if(target == null) return null;
	for(int i=0; i<newParams.size(); i++){
	    final ProgramVariable oldP = (ProgramVariable) oldParams.
		getParameterDeclaration(i).
		getVariableSpecification().getProgramVariable();
	    final ProgramVariable newP = (ProgramVariable) newParams.
		getParameterDeclaration(i).
		getVariableSpecification().getProgramVariable();
	    target = tf.createUpdateTerm(var(oldP), var(newP), target);
	}
	return simplifier.simplify(target, services);
    }
    
    protected Term updatePrefix(Term t){
	if(!pm.isStatic() && t != null && inheritedPrefix != null){
	    t = tf.createUpdateTerm(
		      var((ProgramVariable) inheritedPrefix),
		      var(self), t);
	    t = simplifier.simplify(t, services);
	}
	return t;
    }

}
