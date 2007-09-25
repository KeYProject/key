// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class UsefulTools {

    private static final UpdateSimplifier simplifier = new UpdateSimplifier();

    
    private UsefulTools(){
    }

    /**
     * Checks whether <code>a</code> occurs in <code>b</code> or not. If
     * <code>ignoreMod</code> is true, subterms with a modality as top operant
     * are ignored.
     */
    public static boolean occursIn(Term a, Term b, boolean ignoreMod){
	if(a == null || b == null){
	    return false;
	}	
	if(a.equals(b)){
	    return true;
	}else if(b.op() instanceof Modality && ignoreMod){
	    return false;
	}else{
	    for(int i=0;i<b.arity();i++){
		if(occursIn(a, b.sub(i), ignoreMod)) return true;
	    }
        }
	return false;
    }

    /**
     * Checks whether <code>attr</code> occurs in <code>b</code> and
     * returns the terms of the form t.attr that have been found in 
     * <code>b</code>. If <code>ignoreMod</code> is true, 
     * subterms with a modality as top operant are ignored.
     */
    public static ListOfTerm occursAsAttr(ProgramVariable attr, 
					  Term b, boolean ignoreMod){
	ListOfTerm result = SLListOfTerm.EMPTY_LIST;
	if (b == null){
	    return result;
	}
	if ((b.op() instanceof AttributeOp) && 
	    ((AttributeOp) b.op()).attribute() == attr) {
	    return result.append(b);
	}
	if (b.op() instanceof Modality && ignoreMod){
	    return result;
	}
	for(int i=0;i<b.arity();i++){
	    result = result.append(occursAsAttr(attr, b.sub(i), ignoreMod));
	}	
	return result;
    }

    /**
     * Collects the model variables in <code>b</code>.
     * If <code>ignoreMod</code> is true, 
     * subterms with a modality as top operant are ignored.
     */
    public static SetOfTerm collectModelVariables(Term b, boolean ignoreMod){
	SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
	if(b == null){
	    return result;
	}
	if((b.op() instanceof AttributeOp) && 
	   (((AttributeOp) b.op()).attribute() instanceof ProgramVariable) &&
	   ((ProgramVariable) ((AttributeOp) b.op()).attribute()).isModel()){
	    return result.add(b);
	}
	if((b.op() instanceof ProgramVariable) && 
	   ((ProgramVariable) b.op()).isModel()){
	    return result.add(b);
	}
	if(b.op() instanceof Modality && ignoreMod){
	    return result;
	}
	for(int i=0;i<b.arity();i++){
	    result = result.union(collectModelVariables(b.sub(i), ignoreMod));
	}	
	return result;	
    }

    /**
     * adds updates for represents clauses if necessary. These Updates have the
     * form {m := m()}t 
     * where m is a modelfield and m() is a query generated from the represents
     * clause for m.
     */
    public static Term addRepresents(Term t, Services services, 
				     ProgramVariable self){
	if(t == null) return t;
	SetOfTerm fields = collectModelVariables(t, false);
	if(fields != SetAsListOfTerm.EMPTY_SET){	  
	    IteratorOfTerm it = fields.iterator();	    
            UpdateFactory uf = new UpdateFactory(services, simplifier);
            Update update = null;
            while(it.hasNext()){
		Term field = it.next();
                Term value;               
		if(field.op() instanceof AttributeOp){
		    KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(
			field.sub(0).sort());
		    HashMap rep = services.getImplementation2SpecMap().
			getSpecForClass(kjt).getRepresents();
		    ProgramVariable v = 
			(ProgramVariable) ((AttributeOp) field.op()).
			attribute();                   
		    if(rep.get(v) != null){
			value = simplifyRepresentsMethod(
                                  TermFactory.DEFAULT.createFunctionTerm(
                                             (TermSymbol)((Term) rep.get(v)).op(), 
                                             field.sub(0)), 
                                          services,
                                          self); 
		    }else{
			// This case can occur if the representsclause contains
			// an unsupported JML feature (or if the specification
			// is syntactically invalid).
			value = field;
		    }
		}else{
		    final ProgramVariable v = 
                        (ProgramVariable) field.op();
		    HashMap rep;
		    //		    if(v.isStatic()){
			rep = services.getImplementation2SpecMap().
			    getSpecForClass(v.getContainerType()).
			    getRepresents();
			value = simplifyRepresentsMethod
                              ((Term) rep.get(v), 
                                       services,
                                       self);
			//		    }
		}             
		if (update == null) {
		    update = uf.elementaryUpdate(field, value); 
		} else {
		    update = uf.parallel(update, 
		            uf.elementaryUpdate(field, value));
		}		
            }
	    if (update != null){
                t = uf.apply(update, t);
	    }
	}	
	return t;
    }

    public static Term createTermForQuery(ProgramMethod pm, 
					  ListOfTerm args,
					  ReferencePrefix prefix){
	Term[] sub;
	TermFactory tf = TermFactory.DEFAULT;
	int i=0;
	if(pm.isStatic()){
	    sub = new Term[args.size()];
	}else{
	    sub = new Term[args.size()+1];
	    sub[i++] = 
		tf.createVariableTerm((ProgramVariable) prefix);
	}
	IteratorOfTerm it = args.iterator();
	while(it.hasNext()){
	    sub[i++] = it.next();
	}
	return tf.createFunctionTerm(pm, sub);
    }

    public static ListOfTerm getProgramVariablesFromTerm(Term t, 
							 ListOfTerm result){
	if(t == null){
	    return result;
	}
	if(t.op() instanceof ProgramVariable){
	    if(!result.contains(t)){
		result = result.append(t);
	    }
	}
	for(int i = 0; i<t.arity(); i++){
	    result = getProgramVariablesFromTerm(t.sub(i), result);
	}
	return result;
    }

    public static ParameterDeclaration getParameterDeclForVar(Term var,
							      Services serv){
	ProgramVariable pv = (ProgramVariable) var.op();
	KeYJavaType kjt = pv.getKeYJavaType();
	if(kjt == null){
	    kjt = serv.getJavaInfo().getKeYJavaType(var.sort());
	}
	return new ParameterDeclaration(new Modifier[0], 
					new TypeRef(kjt), 
					new VariableSpecification(pv), 
					false); 
    }

    /** <code>a</code> is a function term for a query. If the specification
     * of this query has a postcondition of the form \result == b then
     * b is returned otherwise a is returned.
     *
     */
    private static Term simplifyRepresentsMethod(Term a, 
						 Services services,
						 ProgramVariable self){
	Implementation2SpecMap ism = services.getImplementation2SpecMap();
	if(a.arity()>0 && a.sub(0).op()==self){
	    TermFactory tf = TermFactory.DEFAULT;
	    ProgramMethod pm = (ProgramMethod) a.op();
	    if(ism.getSpecsForMethod(pm) == null) return a;
	    JMLMethodSpec spec = ism.getSpecsForMethod(pm).iterator().next();
	    Term post = spec.getPost();
	    if(post.op() instanceof Equality  && 
	       collectModelVariables(post, false)==SetAsListOfTerm.EMPTY_SET){
		if(spec.getPrefix() instanceof ProgramVariable &&
		   spec.getPrefix() != self){
		    post = tf.createUpdateTerm(
			tf.createVariableTerm((ProgramVariable) 
					      spec.getPrefix()),
			tf.createVariableTerm(self),
			post);
		    post = simplifier.simplify(post, services);
		    
		}
		if(post.sub(0).op() == spec.getResultVar()){
		    return post.sub(1);
		}else if(post.sub(1).op() == spec.getResultVar()){
		    return post.sub(0);
		}
	    }
	}
	return a;
    }

    /**
     * Checks whether only pure methods have been used in this specification or
     * not.
     * @return null iff every method used in this term is declared 
     * with the jml-modifier pure or a method that isn't declared 
     * with pure otherwise.
     */
    public static ProgramMethod purityCheck(JMLMethodSpec spec, 
					    Implementation2SpecMap ism){
	Term t = spec.createDLFormula(true, false);
	return purityCheck(t, ism);
    }

    /**
     * Checks whether only pure methods have been used in this term or
     * not.
     * @return null iff every method used in this term is declared 
     * with the jml-modifier pure or a method that isn't declared 
     * with pure otherwise.
     */
    public static ProgramMethod purityCheck(Term t,
					    Implementation2SpecMap ism){
	if ( t.op() instanceof ProgramMethod ) {
	    if(!ism.getModifiers((ProgramMethod)t.op()).contains("pure")){
		return (ProgramMethod) t.op();
	    }
	}
        
	for(int i=0;i<t.arity();i++){
	    if(purityCheck(t.sub(i), ism) != null){ 
		return purityCheck(t.sub(i), ism);
	    }
	}
	return null;
    }

    /** 
     * Returns forall self_lv( {self:=self_lv} t ) if <code>t</code> is neither
     * static nor a constructor or <code>t</code> otherwise.
     */
    public static Term quantifySelf(Term t, MethodDeclaration md,
				    ProgramVariable self){
	if(!md.isStatic() && !(md instanceof ConstructorDeclaration)){
	    TermFactory tf = TermFactory.DEFAULT;
	    Term vTerm = tf.createVariableTerm(self);
	    LogicVariable lv = new LogicVariable(new Name(self.name()+"_lv"),
						 self.sort());
	    Term lvTerm = tf.createVariableTerm(lv);
	    t = tf.createUpdateTerm(vTerm, lvTerm, t);
	    t = TermBuilder.DF.all(lv, t);
	}
	return t;
    }

    /** Creates a quantified LogicVariable lv_i for ProgramVariabes p_i in 
     * <code>t</code> that aren't contained in the Namespace <code>ns</code>.
     * @return q lv_1...lv_n {p_1 := lv_1}..{p_n := lv_n} t.
     */
    public static Term quantifyProgramVariables(Term t, Namespace ns,
						Quantifier q, Services serv){
	SetOfNamed pvs = helpQuantify(t, ns.allElements());
	IteratorOfNamed it = pvs.iterator();
	return quantifyProgramVariables(t, it, q, serv);
    }

    public static Term quantifyProgramVariables(Term t, IteratorOfNamed it,
						Quantifier q, Services serv){
	while(it.hasNext()){
	    ProgramVariable v = (ProgramVariable) it.next();
	    t = quantifyProgramVariable(t, v, q, serv);
	}
	return t;
    }

    /**
     * Returns q lv . {v := lv}t
     */
    public static Term quantifyProgramVariable(Term t, ProgramVariable v,
					       Quantifier q, Services serv){
	final TermFactory tf = TermFactory.DEFAULT;
        final TermBuilder df = TermBuilder.DF; 
        Term vTerm = tf.createVariableTerm(v);
        
        final Sort intSort = serv.getTypeConverter().
        getIntegerLDT().targetSort();
        final Sort sort;
        
        if (v.sort().extendsTrans(intSort)) {
            sort = intSort;
        } else {
            sort = v.sort();
        }
        
	LogicVariable lv = new LogicVariable(new Name(v.name()+"_lv"),  sort);
	if(v.getKeYJavaType().getSort() instanceof ObjectSort){
	    
            Term nullComp = df.equals(vTerm, df.NULL(serv));
            Term cnCond   = df.and(isCreated(vTerm, serv), 
                                   df.not(nullComp));
	    cnCond = df.or(cnCond, nullComp);
	    
            if (q == Op.ALL){
		t = df.imp(cnCond, t);
	    }else{
		t = df.and(cnCond, t);
	    }
	}
	Term lvTerm = tf.createVariableTerm(lv);
	t = tf.createUpdateTerm(vTerm, lvTerm, t);
	t = tf.createQuantifierTerm(q, lv, t);
	return t;
    }

    public static Term isCreated(Term objectToGuard, Services s) {
        if (!(objectToGuard.sort() instanceof ObjectSort)) {
            throw new IllegalArgumentException(
                    "Only reference objects can be guarded.");
        }

        final TermBuilder df = TermBuilder.DF;

        final ProgramVariable created = s.getJavaInfo().getAttribute(
                ImplicitFieldAdder.IMPLICIT_CREATED,
                s.getJavaInfo().getJavaLangObject());

        if (created == null) {
            throw new IllegalStateException("missing implict attribute for "
                    + objectToGuard.sort());
        }

        return df.equals(df.dot(objectToGuard, created), 
                         df.TRUE(s));
    }
    
    /**
     * returns all program variables that occur in t and ns.
     */
    private static SetOfNamed helpQuantify(Term t, ListOfNamed ns){
	SetOfNamed pvs = SetAsListOfNamed.EMPTY_SET;
	if(t.op() instanceof ProgramVariable && 
	   !ns.contains(t.op())){
	    pvs = pvs.add(t.op());
	}
	for(int i = 0; i<t.arity(); i++){
	    pvs = pvs.union(helpQuantify(t.sub(i), ns));
	}
	return pvs;
    }

    public static ListOfNamed getParameters(MethodDeclaration md){
	ListOfNamed pl = SLListOfNamed.EMPTY_LIST;
        if(md != null && md.getParameters().size() != 0){
            ArrayOfParameterDeclaration params = md.getParameters();
            for(int i=0; i<params.size(); i++){
                ProgramVariable p = (ProgramVariable) params.
		    getParameterDeclaration(i).
		    getVariableSpecification().getProgramVariable();
                pl = pl.append(p);
            }
        }
	return pl;
    }

    public static Namespace buildParamNamespace(MethodDeclaration md){
	return buildParamNamespace(md, null, null);
    }

    public static Namespace buildParamNamespace(MethodDeclaration md, 
						LinkedList args,
						HashMap argMap){
	Namespace param_ns = new Namespace();
        if(md != null && md.getParameters().size() != 0){
            ArrayOfParameterDeclaration params = md.getParameters();
            for(int i=0; i<params.size(); i++){
                ProgramVariable p = (ProgramVariable) params.
		    getParameterDeclaration(i).
		    getVariableSpecification().getProgramVariable();
		if(argMap!=null && args!=null && !args.isEmpty()){
		    param_ns.add((ProgramVariable) args.get(i));
		    argMap.put(args.get(i), p);
		}else{
		    param_ns.add(p);
		}
            }
        }
	return param_ns;
    }

    /**
     * creates <{typeof(vTerm) v;}> q lv ({vTerm := lv} body) 
     * where v = vTerm.op()
     */
    public static Term createQuantifierTermWithPV(
	Quantifier q, Term vTerm, LogicVariable lv, Term body){
	TermFactory tf = TermFactory.DEFAULT;
	Term result;
	body = tf.createUpdateTerm(vTerm, tf.createVariableTerm(lv), body);
	result = tf.createQuantifierTerm(q, lv, body);
	//adds a declaration for the programvariable if necessary
	ProgramVariable v = (ProgramVariable) vTerm.op();
	LocalVariableDeclaration vDecl = new LocalVariableDeclaration
	    (new TypeRef(v.getKeYJavaType()), 
	     new VariableSpecification(v)); 
	JavaBlock jb = 
	    JavaBlock.createJavaBlock(new StatementBlock(vDecl));
	result = tf.createDiamondTerm(jb, result);
	return result;
   }

    /**
     * Returns a conjunction of the terms returned by getAllInvariants() for
     * every <code>JMLClassSpec</code>.
     */
    public static Term allInvariants(Implementation2SpecMap ism){
	if(ism.allInvariants() != null) return ism.allInvariants();
	Term result = null;

	Iterator it  = ism.getAllClasses().iterator();
	Namespace ns = new Namespace();

	while(it.hasNext()){
	    KeYJavaType kjt = (KeYJavaType) it.next();
	    JMLClassSpec cs = ism.getSpecForClass(kjt);
	    Term inv = cs.getAllLocalInvariants();
	    ns.add(cs.getProgramVariableNS().allElements());
	    if(inv != null){
		if(result == null){
		    result = inv;
		}else{
		    result = TermBuilder.DF.and(result, inv);
		}
	    }
	}
	ism.setAllInvPVNS(ns);
	ism.setAllInvariants(result);
	return result;
    }

    private static boolean containsQuery(Term t){
	if(t.op() instanceof ProgramMethod){
	    return true;
	}
	for(int i=0; i<t.arity(); i++){
	    if(containsQuery(t.sub(i))){
		return true;
	    }
	}
	return false;
    }

    /** 
     * returns true if c contains a jml keyword that does not occur in 
     * methodspecs
     */
    public static boolean isClassSpec(Comment c){
	if(!c.containsJMLSpec()){
	    return false;
	} 
	String spec = c.getJMLSpec();
	return (spec.indexOf(" invariant") != -1 ||
	    spec.indexOf(" constraint") != -1 ||
	    spec.indexOf(" invariant_redundantly") != -1 ||
	    spec.indexOf(" constraint_redundantly") != -1 ||
	    spec.indexOf(" model ") != -1 ||
	    spec.indexOf(" ghost ") != -1 ||
	    spec.indexOf(" represents") != -1 ||
	    spec.indexOf(" monitors_for") != -1 ||
	    spec.indexOf(" writable") != -1 ||
	    spec.indexOf(" readable") != -1 ||
	    spec.indexOf(" initially") != -1 ||
	    spec.indexOf(" axiom") != -1);
    }


    public static Term makeConjunction(Term t1, Term t2){
	if(t2 != null){
	    if(t1 == null){
		return t2;
	    }else{
		return TermBuilder.DF.and(t1, t2);
	    }
	}
	return t1;
    }

}
