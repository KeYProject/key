// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.jml;

import java.util.HashMap;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.Constructor;
import de.uka.ilkd.key.java.abstraction.IteratorOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Model;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.Static;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.recoderext.ClassInitializeMethodBuilder;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;

/** wraps specifications that are valid for the entire class (e.g. invariants
 * or history constraints) or interface
 */
public class JMLClassSpec extends JMLSpec {

    private Term instInv, instCon, staticInv, staticCon;
    private LinkedHashMap term2old;
    private LinkedHashMap represents;
//    private HashMap suchthat;
    private ReferencePrefix staticPrefix;
    private ReferencePrefix instancePrefix;
    private Services services;       
    /** the class or interfacedeclaration this specification refers to */
    private TypeDeclaration cd;
    // the KeYJavaType of cd
    private KeYJavaType type;
    private Namespace modelVars;
    private Namespace modelMethods;
    private NamespaceSet nss;
    private KeYJavaType objectKeYJavaType;
    protected static Term trueTerm = null;
    protected static Term falseTerm = null;
    private String javaPath;
    
    // flag which is set to false iff static initialisation features should be suppressed
    protected boolean staticInit=false;

    public JMLClassSpec(Services services, TypeDeclaration cd, 
            NamespaceSet nss, String javaPath){
	
        progVarNS = new Namespace();
	funcNS = new Namespace();
	
        
        term2old = new LinkedHashMap();
	this.services = services;
        objectKeYJavaType = services.getJavaInfo().getJavaLangObject();        
        
	this.cd   = cd;
        instCon   = null;
        staticCon = null;
        instInv   = null;
        staticInv = null;
        
        type = services.getJavaInfo().getKeYJavaType(cd);
	staticPrefix = new TypeRef(type);
	instancePrefix = new LocationVariable(
	    new ProgramElementName("self_"+cd.getName().replace('.', '_')
				   .replace('<', '_').replace('>', '_')), 
	    type);
	progVarNS.add((ProgramVariable) instancePrefix);	
	modelVars = new Namespace();
	modelMethods = new Namespace();
	represents = new LinkedHashMap();
//	suchthat = new HashMap();
	this.nss = nss;
	services.getImplementation2SpecMap().addClassSpec(this);        
	if(trueTerm == null){
	    trueTerm = tt();
	}
	if(falseTerm == null){
	    falseTerm = ff();
	}
        this.javaPath = javaPath;
    }

    public boolean containsInvOrConst(){
	return (staticCon != null ||
	    staticInv != null ||
	    instCon != null ||
	    instInv != null);
    }

    public Services getServices(){
	return services;
    }

    /** 
     * returns the class or interfacedeclaration this specification refers to. 
     */
    public TypeDeclaration getClassDeclaration(){
	return cd;
    }

    public ReferencePrefix getInstancePrefix(){
	return instancePrefix;
    }

    public ReferencePrefix getStaticPrefix(){
	return staticPrefix;
    }
    
    public void addInstanceInvariant(Term t){
	instInv = UsefulTools.makeConjunction(instInv,t);
    }

    public void addStaticInvariant(Term t){
	staticInv = UsefulTools.makeConjunction(staticInv, t);
    }

    public void addInstanceConstraint(Term t){
	instCon = UsefulTools.makeConjunction(instCon, t);
    }

    public void addStaticConstraint(Term t){
	staticCon = UsefulTools.makeConjunction(staticCon, t);
    }

    public void addModelVariable(ProgramVariable v){
	//	nss.programVariables().add(v);
	modelVars.add(v);
	if(cd instanceof InterfaceDeclaration){
	    addRepresents(v, null);
	}
    }

    public void addModelMethod(ProgramMethod pm){
	modelMethods.add(pm);
    }

    /**
     * returns the model variables declared in this class
     */
    public Namespace getModelVars(){
	return modelVars;
    }

    /**
     * returns the model methods declared in this class
     */
    public Namespace getModelMethods(){
	return modelMethods;
    }

    /** 
    * adds the representation <code>rep</code> for the model variable 
    * <code>var</code>.
    */
   public void addRepresents(Term loc, Term rep) {
        addRepresents(getPV((Location) loc.op()), rep);
    }
    
    /** 
     * adds the representation <code>rep</code> for the model variable 
     * <code>var</code>.
     */
    public void addRepresents(ProgramVariable v, Term rep){
	ProgramMethod pm =createProgramMethodForMV(v);
        modelMethods.add(pm);
        if (rep != null) {
            JMLMethodSpec spec = new JMLNormalMethodSpec(pm, services,
                    new Namespace(), new LinkedHashMap(), this, nss, javaPath);
            spec.setAssignableMode("nothing");
            if (rep.sort() == Sort.FORMULA) {
                if ((rep.op() instanceof Equality) && rep.sub(1) != null
                        && rep.sub(1).equals(JMLMethodSpec.BOOL_TRUE)) {
                    spec.addPost(equals(var(spec.getResultVar()), rep.sub(0)));
                } else if (rep.op() == Op.TRUE) {
                    spec.addPost(equals(var(spec.getResultVar()), JMLMethodSpec.BOOL_TRUE));
                } else {
                    Term eq = equals(var(spec.getResultVar()), JMLMethodSpec.BOOL_TRUE);                    
                    spec.addPost(equiv(eq, rep));
                }
            } else {
                spec.addPost(equals(var(spec.getResultVar()), rep));
            }
        }        
        represents.put(v, getTermForModelMethod(pm));
    }

    /**
     * the loc is either a programvariable or an attribute
     * in the first case loc itself in the latter one loc.attribute()
     * is returned    
     */
    private ProgramVariable getPV(Location loc) {       
        if(loc instanceof ProgramVariable){
            return (ProgramVariable) loc;
        }
        return (ProgramVariable) ((AttributeOp) loc).attribute();       
    }
    
    public void addSuchThat(Term t_loc, Term axiom) {
        ProgramVariable v = getPV((Location)t_loc.op());
        ProgramMethod pm = createProgramMethodForMV(v);
        
        
        represents.put(v, getTermForModelMethod(pm));
        modelMethods.add(pm);
        JMLMethodSpec spec = new JMLNormalMethodSpec(
                pm, services,
                new Namespace(), new LinkedHashMap(), this, nss, javaPath);
        spec.setAssignableMode("nothing");
        spec.addPost(tf.createUpdateTerm(
			 t_loc, 
			 var(spec.getResultVar()),
			 axiom));
	spec.addPre(getExTermForModelVar(t_loc, axiom));
    }

    /** 
     * returns a mapping from modelmethods to their specifications.
     */
    public HashMap buildModelMethod2Specs(){
	HashMap modelMethod2Specs = new HashMap();
	IteratorOfNamed it = modelMethods.allElements().iterator();
	Implementation2SpecMap ism = services.getImplementation2SpecMap();
	while(it.hasNext()){
	    ProgramMethod pm = (ProgramMethod) it.next();
	    modelMethod2Specs.put(pm, 
				  ism.getSpecsForMethod(pm));
	}
	return modelMethod2Specs;
    }

    /**
     * returns a HashMap that contains the locally defined and inherited 
     * represents relations.
     */
    public HashMap getRepresents(){
	HashMap result = new HashMap();
	KeYJavaType kjt = services.getJavaInfo().getSuperclass(type);
	if(kjt == null){
	    kjt = objectKeYJavaType;
	}
	JMLClassSpec superSpec = 
	    services.getImplementation2SpecMap().getSpecForClass(kjt);
	if(superSpec != null && (cd instanceof ClassDeclaration) && 
	   type != objectKeYJavaType){
	    result.putAll(superSpec.getRepresents());
	}
	result.putAll(represents);
	return result;
    }

    public LinkedHashMap getTerm2Old(){
	return term2old;
    }

    public Term getLocalInstanceInvariants(){
	return instInv;
    }

    public SetOfTerm getAllQuantifiedInvariants() {
        return getQuantifiedInstanceInvariants().add(staticInv);
    }

    public SetOfTerm getQuantifiedInstanceInvariants() {
        Term result = null;
        Term self = tf.createVariableTerm((ProgramVariable) instancePrefix);
        if(getInstanceInvariants() != null && 
           !trueTerm.equals(getInstanceInvariants())){
            Term eqn = not(equals(self, NULL(services)));          
            ProgramVariable created = services.getJavaInfo().getAttribute(
                ImplicitFieldAdder.IMPLICIT_CREATED, objectKeYJavaType);
            Term eqc = equals(dot(self, created), JMLMethodSpec.BOOL_TRUE);        
            result = imp(and(eqn, eqc), getInstanceInvariants());
            result = UsefulTools.addRepresents(result, services, 
                                            (ProgramVariable) instancePrefix);
            LogicVariable selfLv = 
                new LogicVariable(new Name("self_"+cd.getName()+
                                           "_lv"),
                                  self.sort());            
            result = tf.createUpdateTerm(self, var(selfLv), result);
            result = all(selfLv, result);
        }
        if(result == null){
            return SetAsListOfTerm.EMPTY_SET;
        }
        result = UsefulTools.addRepresents(result, services, 
                                           (ProgramVariable) instancePrefix);
        return SetAsListOfTerm.EMPTY_SET.add(result);
    }
    
    /**
     * returns locally declared and inherited instance invariants. 
     */
    public Term getInstanceInvariants(){
	Term result = UsefulTools.makeConjunction(null, instInv);
	Implementation2SpecMap ism = services.getImplementation2SpecMap();
	ListOfKeYJavaType l = cd.getSupertypes();
	IteratorOfKeYJavaType it = l.iterator(); 
	while(it.hasNext()){
	    JMLClassSpec cs = ism.getSpecForClass(it.next());
	    if(cs != null){
		Term ii = cs.getInstanceInvariants();
		if(ii != null){
		    Term upd = tf.createUpdateTerm(
                         var((ProgramVariable)cs.getInstancePrefix()),
			 var((ProgramVariable)getInstancePrefix()),
			 ii);
		    result = UsefulTools.makeConjunction(result, upd);
		    progVarNS.add(cs.getProgramVariableNS().allElements());
		}
	    }
	}
	return result;
    }

    public Term getLocalStaticInvariants(){
	return staticInv;
    }

    public Term getStaticInvariants(){
	Term result = staticInv;
	Implementation2SpecMap ism = services.getImplementation2SpecMap();
	ListOfKeYJavaType l = cd.getSupertypes();
	IteratorOfKeYJavaType it = l.iterator(); 
	while(it.hasNext()){
	    JMLClassSpec cs = ism.getSpecForClass(it.next());
	    if(cs != null){
		result = UsefulTools.makeConjunction(
		    result, cs.getStaticInvariants());
		progVarNS.add(cs.getProgramVariableNS().allElements());
	    }
	}
	return result;
    }

    public Term getLocalInstanceConstraints(){
	return instCon;
    }

    public Term getInstanceConstraints(){
	Term result = instCon;
	Implementation2SpecMap ism = services.getImplementation2SpecMap();
	ListOfKeYJavaType l = cd.getSupertypes();
	IteratorOfKeYJavaType it = l.iterator(); 
	while(it.hasNext()){
	    JMLClassSpec cs = ism.getSpecForClass(it.next());
	    if(cs != null){
		Term ic = cs.getInstanceConstraints();
		if(ic != null){
		    Term upd = tf.createUpdateTerm(
			 var((ProgramVariable)cs.getInstancePrefix()),
			 var((ProgramVariable)getInstancePrefix()),
			 ic);
		    result = UsefulTools.makeConjunction(result, upd);
		    progVarNS.add(cs.getProgramVariableNS().allElements());
		}
	    }
	}
	return result;
    }

    public Term getLocalStaticConstraints(){
	return staticCon;
    }

    public Term getStaticConstraints(){
	Term result = staticCon;
	Implementation2SpecMap ism = services.getImplementation2SpecMap();
	ListOfKeYJavaType l = cd.getSupertypes();
	IteratorOfKeYJavaType it = l.iterator(); 
	while(it.hasNext()){
	    JMLClassSpec cs = ism.getSpecForClass(it.next());
	    if(cs != null){
		result = UsefulTools.makeConjunction(
		    result, cs.getStaticConstraints());
		progVarNS.add(cs.getProgramVariableNS().allElements());
	    }
	}
	return result;
    }

    /** generates \exists x . p(x) where p is the relation for 
     * <code>modelvar</code> described by its represents-such_that clause.
     */
    public Term getExTermForModelVar(Term modelVar, Term axiom){
	LogicVariable lv = new LogicVariable(new Name(modelVar.toString()+
						 "_jml_lv"), modelVar.sort());
	Term result = tf.createUpdateTerm(modelVar, var(lv), axiom);
	return ex(lv, result);
    }

    public ProgramVariable lookupModelField(Name name)
	throws AmbigiousModelElementException{
	if(modelVars.lookup(name) != null){
	    return (ProgramVariable) modelVars.lookup(name);
	}
	Implementation2SpecMap ism = services.getImplementation2SpecMap();
	ListOfKeYJavaType st = cd.getSupertypes();
	boolean hasNonInterfaceST = false;
	IteratorOfKeYJavaType it = st.iterator();
	ProgramVariable result = null;
	while(it.hasNext()){
	    KeYJavaType kjt = it.next();
	    if((kjt.getJavaType() instanceof ClassDeclaration)){
		hasNonInterfaceST = true;
	    } 
	    JMLClassSpec cs = ism.getSpecForClass(kjt);
	    if(cs != null){
		ProgramVariable p = cs.lookupModelField(name);
		if(p != null){
		    if(result == null){
			result = p;
		    }else{
			//		    throw new AmbigiousModelElementException(result);
		    }
		}
	    }
	}
	if(result == null && type != objectKeYJavaType && !hasNonInterfaceST ){
	    if(ism.getSpecForClass(objectKeYJavaType) == null){
		return result;
	    }
	    result = ism.getSpecForClass(objectKeYJavaType).
		lookupModelField(name);
	}
	return result;
    } 
    
    /**
     * Returns the Term ((self!=null & self.created=true) -> instanceInvariants
     * ) & staticInvariants, which is sometimes needed in POs.  
     */
    public Term getAllLocalInvariants(){
	Term result = null;
	Term self = var((ProgramVariable) instancePrefix);
	if(getLocalInstanceInvariants() != null && 
	   !trueTerm.equals(getLocalInstanceInvariants())){
	    final Term eqn = not ( equals(self, NULL(services)) );	    	    
	    final Term eqc = UsefulTools.isCreated(self, services);
	
	    result = imp ( and ( eqn, eqc ), getLocalInstanceInvariants() );
	
            result = UsefulTools.addRepresents(result, services, 
					    (ProgramVariable) instancePrefix);
	    LogicVariable selfLv = 
		new LogicVariable(new Name("self_"+cd.getName()+
					   "_lv"),
				  self.sort());	    
	    result = tf.createUpdateTerm(self, var(selfLv), result);
	    result = all(selfLv, result);
	}
	if(getLocalStaticInvariants() != null &&
	   !trueTerm.equals(getLocalStaticInvariants())){
	    Term si;
	    if(staticInit){
		ProgramVariable ci = services.getJavaInfo().getAttribute(
		    ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, type);
		si = equals ( var(ci), JMLMethodSpec.BOOL_TRUE );
		si = imp ( si, getLocalStaticInvariants() );
	    }else{
		si = getLocalStaticInvariants();
	    }
	    si = UsefulTools.addRepresents(si, services, 
					   (ProgramVariable) instancePrefix);
	    result = UsefulTools.makeConjunction(result, si);
	}
	if(result == null){
	    return null;
	}
	result = UsefulTools.addRepresents(result, services, 
					   (ProgramVariable) instancePrefix);
	return result;
    }

    /**
     * returns the model method with the name <code>name</code>, 
     * iff it is loacally declared within the type that is specified by this
     * specification.
     */
    public ProgramMethod lookupModelMethodLocally(String name){
	if(modelMethods.lookup(new Name(type.getSort().toString()+
					"::"+name)) != null){
	    return (ProgramMethod) modelMethods.lookup(
		     new Name(type.getSort().toString()+"::"+name.toString()));
	}
	return null;
    }

    public ProgramMethod lookupModelMethod(Name name)
	throws AmbigiousModelElementException{
	if(modelMethods.lookup(new Name(type.getSort().toString()+
					"::"+name.toString())) != null){
	    return (ProgramMethod) modelMethods.lookup(
		     new Name(type.getSort().toString()+"::"+name.toString()));
	}
	Implementation2SpecMap ism = services.getImplementation2SpecMap();
	ListOfKeYJavaType st = cd.getSupertypes();
	IteratorOfKeYJavaType it = st.iterator();
	ProgramMethod result = null;
	while(it.hasNext()){
	    KeYJavaType kjt = it.next();
	    if(ism.getSpecForClass(kjt) != null &&
	       ism.getSpecForClass(kjt).lookupModelMethod(name) != null){
		if(result == null){
		    result = ism.getSpecForClass(kjt).lookupModelMethod(name);
		}else{
		    throw new AmbigiousModelElementException(result);
		}
	    }
	}
	return result;
    } 

    protected Term getTermForModelMethod(ProgramMethod pm){
	Term[] sub;
	if(pm.isStatic()){
	    sub = new Term[0];
	}else{
	    sub = new Term[1];
	    sub[0] = var((ProgramVariable) instancePrefix);
	}
	return func(pm, sub);
    }
    
    /**
     * creates a ProgramMethod and the Term for substituting the 
     * corresponding Model Variable.
     */
    private ProgramMethod createProgramMethodForMV(ProgramVariable mv){
	ExtList l = new ExtList();	
	l.add(new ProgramElementName(mv.name().toString()+"_rep"));
	if(mv.isStatic()){
	    l.add(new Static());
	}
	l.add(new Model());
	l.add(new Public());
	l.add(new TypeRef(mv.getKeYJavaType()));
	MethodDeclaration md = new MethodDeclaration(l, false);
	ProgramMethod pm = new ProgramMethod(md, type, 
					     mv.getKeYJavaType(),
					     PositionInfo.UNDEFINED);
	services.getImplementation2SpecMap().addModifier(pm, "pure");
	services.getImplementation2SpecMap().addModifier(pm, "helper");
	if(nss.functions().lookup(pm.name()) == null){
	    nss.functions().add(pm);
	}
	return pm;
    }

    /**
     * returns a term of the form inv -> <{try{ m();}catch(Exception e)}>inv
     * If <code>allInv</code> is true, inv is a conjunction of all
     * (static and instance) invariants of every existing type or just
     * the invariants of this type specification otherwise.
     */
    public Term getPreservesInvariantBehavior(ProgramMethod md,
					      boolean allInv){
	if(!services.getImplementation2SpecMap().
	   getModifiers(md).contains("helper") && (
	       !md.isStatic() &&(getInstanceInvariants()!=null ||
				 getInstanceConstraints()!=null) ||
	       getStaticInvariants() != null ||
	       getStaticConstraints() != null || allInv)){
	    Term excPre, excPost, result;
	    result = excPre = excPost = null;
	    KeYJavaType exc = 
		services.getJavaInfo().getTypeByClassName("java.lang.Exception");
	    Branch[] catches = new Branch[1];
	    StatementBlock catchBody = new StatementBlock();
	    ProgramVariable e = new LocationVariable(
		new ProgramElementName("_exc"+
				       (JMLMethodSpec.exceptionVarCount++)), 
		exc);
	    progVarNS.add(e);
	    ParameterDeclaration param = 
		new ParameterDeclaration(new Modifier[0], new TypeRef(exc),
					 new VariableSpecification(e), false);
	    catches[0] = new Catch(param, catchBody);
	    excPost = addClassSpec2Post(excPost, true, !allInv, md, this);
	    excPost = UsefulTools.addRepresents(excPost, services, 
				      (ProgramVariable) instancePrefix);
	    if(allInv){
		Term ai = UsefulTools.
		    allInvariants(services.getImplementation2SpecMap());
		excPre = UsefulTools.makeConjunction(ai, excPre);
		excPost = UsefulTools.makeConjunction(ai, excPost);
	    }else{
		excPre = addClassSpec2Pre(excPre, md, this);
	    }
	    StatementBlock tryBlock = 
		new StatementBlock(new Try(makeMBS(md.getMethodDeclaration()), 
					   catches));                        
            
	    JavaBlock jb = JavaBlock.createJavaBlock(tryBlock);
	    if(excPost == null){
		return trueTerm;
	    }
	    excPost = box(jb, excPost);
	    if(excPre == null){
		result = excPost;
	    }else{
		result =imp(excPre,excPost);
	    }
	    result = JMLMethodSpec.
                addOldQuantifiers(result, getTerm2Old(), false, null);
	    result = UsefulTools.addRepresents(result, services, 
					       (ProgramVariable) instancePrefix);
/*	    if(UsefulTools.purityCheck(result, 
				       services.getImplementation2SpecMap()) 
	       != null){
		throw new RuntimeException("Nonpure method "+
					   UsefulTools.purityCheck(result, 
					       services.
					       getImplementation2SpecMap())+
					   " used in the "+
					   "specification for class/interface "
					   + cd.getName());
					   }*/

	    //disjoins the methods preconditions
	    SetOfJMLMethodSpec specs = 
		services.getImplementation2SpecMap().getSpecsForMethod(md);
	    if(specs != null){
		specs = specs.union(services.getImplementation2SpecMap().
				    getInheritedMethodSpecs(md, type));
	    }
	    if(specs != null){
		Term invPre = falseTerm;
		IteratorOfJMLMethodSpec it = specs.iterator();
		while(it.hasNext()){
		    JMLMethodSpec ms = it.next();
		    if(!(ms instanceof JMLPuritySpec)){
			invPre = or ( ms.getCompletePre(false, false, false), 
			              invPre );
		    }
		}
		if(invPre != falseTerm){
		    result = imp ( invPre, result );
		}
	    }
	    result = imp ( selfIsCreatedAndNotNull((ProgramVariable) getInstancePrefix()),
		           result );
	    result = UsefulTools.quantifySelf(result, md.getMethodDeclaration(), 
	    		(ProgramVariable) getInstancePrefix());
	    result = UsefulTools.quantifyProgramVariables(result, 
			    UsefulTools.getParameters(md.getMethodDeclaration()).iterator(), 
			    Op.ALL, services);
            return imp(func(services.getJavaInfo().getInReachableState()), result);
	}else{
	    return trueTerm;
	}
    }

    private Term selfIsCreatedAndNotNull(ProgramVariable self) {
	final Term selfAsTerm = var(self);
	return and ( not ( equals ( selfAsTerm, NULL(services) ) ), 
                UsefulTools.isCreated(selfAsTerm, services) );

    }

    /** Adds the applicable invariants of cSpec to the precondition of md 
     * iff md isn't declared with the modifier helper. md must be a member
     * method of cSpec. 
     */
    public Term addClassSpec2Pre(Term pre, ProgramMethod md, 
				 JMLClassSpec cSpec){
	Term result;
	if(md.getName().equals
	        (ClassInitializeMethodBuilder.CLASS_INITIALIZE_IDENTIFIER)){
	    
            final ProgramVariable classInit = services.getJavaInfo().getAttribute(
	            ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, type);
	    
            result = equals ( var(classInit), JMLMethodSpec.BOOL_FALSE );
	    if (pre != null) { result = and ( pre, result ); }
	    
            
	    final ProgramVariable classErroneous = services.getJavaInfo().getAttribute
	    (ImplicitFieldAdder.IMPLICIT_CLASS_ERRONEOUS, type);
	    result = and ( result, 
	                   equals(var(classErroneous), JMLMethodSpec.BOOL_FALSE));
	    
	    final ProgramVariable classInitInProgress = services.getJavaInfo().
	    getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INIT_IN_PROGRESS, 
	            type);
	    return and ( result, equals( var(classInitInProgress),
	                    JMLMethodSpec.BOOL_FALSE ) );	  
	} else {
	    result = pre;
        }
        
	if(cSpec == null || md.getName().startsWith("<") ||
                services.getImplementation2SpecMap().getModifiers(md).contains("helper")){
	    return pre;
	}
        
	result = UsefulTools.makeConjunction(result, cSpec.getStaticInvariants());
        
	if(!md.isStatic() && 
	   !(md.getMethodDeclaration() instanceof ConstructorDeclaration)){
	    result = UsefulTools.makeConjunction(
		result, cSpec.getInstanceInvariants());
	}
//	result = addAxioms2Pre(result, true, false);
	return result;
    }

    /** Adds invariants and history constraints to the postcondition iff md 
     * isn't declared with the modifier helper.
     */
    public Term addClassSpec2Post(Term post, boolean constraints,
				  boolean invariants,
				  ProgramMethod md, 
				  JMLClassSpec cSpec){
	if(cSpec == null || 
	   services.getImplementation2SpecMap().getModifiers(md).
	   contains("helper")){
	    return post;
	}
	Term result = post == null ? tt() : post;
	if((!md.getName().startsWith("<") || 
	        md.getName().equals
	        (ClassInitializeMethodBuilder.CLASS_INITIALIZE_IDENTIFIER)) && 
	        invariants){
	    result = UsefulTools.makeConjunction(
		result, cSpec.getStaticInvariants());
	}
	if(constraints && !md.getName().startsWith("<")){
	    result = UsefulTools.makeConjunction(
		result, cSpec.getStaticConstraints());
	}
	if(!md.isStatic() && !md.getName().startsWith("<")){
	    if(invariants){
		result = UsefulTools.makeConjunction(
		    result, cSpec.getInstanceInvariants());
	    }
	    if (constraints && !(md.isConstructor())){
		result = UsefulTools.makeConjunction(
		    result, cSpec.getInstanceConstraints());
	    }
	}
	return and(func(services.getJavaInfo().getInReachableState()), 
                result);
    }

    private StatementBlock makeMBS(MethodDeclaration md){
	StatementBlock mBS;
	ArrayOfParameterDeclaration params = md.getParameters();
	Expression[] aop = new Expression[md.getParameters().size()]; 
	ProgramVariable result = null;
	for(int i=0; i<params.size(); i++){
		aop[i] = (ProgramVariable) params.
		    getParameterDeclaration(i).
		    getVariableSpecification().getProgramVariable();
	}
	if(!(md instanceof Constructor)){
	    KeYJavaType returnType;
	    if(md.getTypeReference() == null){
		returnType = services.getJavaInfo().getKeYJavaType("void");
	    }else{
		returnType = md.getTypeReference().getKeYJavaType();
		result = 
		    new LocationVariable(new ProgramElementName(
					  "_jmlresult"+
					  (JMLMethodSpec.resultVarCount++)),
					returnType);
		progVarNS.add(result);
	    }
	    ProgramMethod pm = 
		new ProgramMethod(md, type, 
				  returnType, PositionInfo.UNDEFINED);
	    MethodBodyStatement mb = new MethodBodyStatement(
		pm,
		pm.isStatic() ? null : getInstancePrefix(),
		result,
		new ArrayOfExpression(aop));
	    mBS = new StatementBlock(mb);
	}else{
	    final TypeRef typeRef = new TypeRef(type);
	    New n = new New(aop,
			    typeRef,
			    null);
	    mBS = new StatementBlock(new CopyAssignment(
	            (ProgramVariable) getInstancePrefix(),
	            n
	    ));
            mBS = new StatementBlock(new MethodFrame(null, new ExecutionContext(typeRef, null), mBS));
	}
	return mBS;
    }

    public String toString(){
	return "Class specification for class "+cd.getName();
    }
   
}

