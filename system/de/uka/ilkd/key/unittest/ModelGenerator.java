// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.unittest.simplify.*;
import de.uka.ilkd.key.unittest.cogent.*;
import java.util.*;

public class ModelGenerator{

    //debug info
    public static int cached = 0; 

    public static final int COGENT = 0;
    public static final int SIMPLIFY = 1;
    public static int decProdForTestGen=COGENT;

    private ListOfTerm ante, succ;
    private HashMap term2class;
    // Maps a location to the set of formulas it occurs in.
    private HashMap eqvC2constr;
    private Services serv;
    private SetOfTerm locations = SetAsListOfTerm.EMPTY_SET;
    private SetOfProgramVariable pvs = SetAsListOfProgramVariable.EMPTY_SET;
    private Node node;
    private Constraint userConstraint;
    private String executionTrace;

    private Node originalNode;

    public ModelGenerator(Services serv, Constraint userConstraint, Node node,
			  String executionTrace, Node originalNode){
	IteratorOfConstrainedFormula itc = 
	    node.sequent().antecedent().iterator();
	ante = SLListOfTerm.EMPTY_LIST;
	while(itc.hasNext()){
	    ante = ante.append(itc.next().formula());
	}
	itc = node.sequent().succedent().iterator();
	succ = SLListOfTerm.EMPTY_LIST;
	while(itc.hasNext()){
	    succ = succ.append(itc.next().formula());
	}
	this.node = node;
        this.originalNode = originalNode;
	this.userConstraint = userConstraint;
	this.serv = serv;
	this.executionTrace = executionTrace;
	eqvC2constr = new HashMap();
	createEquivalenceClassesAndConstraints();
	findBounds();
	findDisjointClasses();
	collectProgramVariables();
    }

    public static boolean isLocation(Term t, Services serv){
	OpCollector oc = new OpCollector();
	t.execPostOrder(oc);
	if(oc.contains(Op.NULL)){
	    return false;
	}
	return t.op() instanceof AttributeOp && checkIndices(t, serv) &&
	    !((ProgramVariable) 
	      ((AttributeOp) t.op()).attribute()).isImplicit() || 
	    t.op() instanceof ProgramVariable && 
	    !((ProgramVariable) t.op()).isImplicit() ||
	    t.op() instanceof ArrayOp && checkIndices(t, serv) ||
	    t.op() instanceof RigidFunction && t.arity()==0 &&
	    !"#".equals(t.op().name().toString()) &&
	    !"TRUE".equals(t.op().name().toString()) &&
	    !"FALSE".equals(t.op().name().toString()) &&
	    t.op().name().toString().indexOf("undef(")==-1;
    }

    /**
     * Returns the associated ExecutionTrace as a String.
     */
    public String getExecutionTrace(){
	return executionTrace;
    }

    /**
     * Returns true iff no negative array indices are contained in t.
     */
    public static boolean checkIndices(Term t, Services serv){
	if(t.op() instanceof AttributeOp){
	    return checkIndices(t.sub(0), serv);
	}
	if(t.op() instanceof ArrayOp){
	    if(t.sub(1).op().name().toString().equals("Z")){
		if(AbstractMetaOperator.convertToDecimalString(
		       t.sub(1), serv).startsWith("-")){
		    return false;
		}
	    }
	    return checkIndices(t.sub(0), serv);
	}
	return true;
    }

    /** Ensures the existence of an EquivalenceClass for each location and 
     * logic variable found
     * in <code>t</code> and updates the mapping from this class to the
     * formulas it occurs in.
     */
    private void collectLocations(Term t){
	if(isLocation(t, serv)){
	    getEqvClass(t);
	    locations = locations.add(t);
	    SetOfTerm constr = (SetOfTerm) eqvC2constr.get(t);
	    if(constr == null){
		constr = SetAsListOfTerm.EMPTY_SET;
	    }
	    eqvC2constr.put(t, constr.add(t));
	}
	if(!(t.op() instanceof Modality || t.op() instanceof IUpdateOperator ||
	     t.op() instanceof Quantifier)){
/*	    if(t.op() instanceof IUpdateOperator){
		IUpdateOperator uop = (IUpdateOperator) t.op();
		for(int i = 0; i<uop.locationCount(); i++){
		    collectLocations(uop.value(t, i));
		}
		}*/
	    for(int i=0; i<t.arity(); i++){
		collectLocations(t.sub(i));
	    }
	}
    }

    public static boolean containsImplicitAttr(Term t){
	if(t.op() instanceof AttributeOp &&
	   ((ProgramVariable) 
	    ((AttributeOp) t.op()).attribute()).isImplicit() ||
	   t.op() instanceof ProgramVariable && 
	   ((ProgramVariable) t.op()).isImplicit()){
	    return true;
	}
	for(int i=0; i<t.arity(); i++){
	    if(containsImplicitAttr(t.sub(i))){
		return true;
	    }
	}
	return false;
    }

    /**
     * Returns the set of locations occuring in node.
     */
    public SetOfTerm getLocations(){
	return locations;
    }

    /**
     * Collects the program variables occuring in node.
     */
    public void collectProgramVariables(){
	IteratorOfTerm it = locations.iterator();
	while(it.hasNext()){
	    Term t = it.next();
	    if((t.op() instanceof ProgramVariable) && 
	       !((ProgramVariable) t.op()).isStatic()){
		pvs = pvs.add((ProgramVariable) t.op());
	    } else if (t.op() instanceof RigidFunction){
		KeYJavaType kjt; 
		if(t.sort().toString().startsWith("jint") ||
		   t.sort().toString().startsWith("jshort") ||
		   t.sort().toString().startsWith("jbyte") ||
		   t.sort().toString().startsWith("jlong") ||
		   t.sort().toString().startsWith("jchar")){	 
		    kjt = serv.getJavaInfo().getKeYJavaType(
			t.sort().toString().substring(1));	 
		}else{
		    kjt = serv.getJavaInfo().getKeYJavaType(t.sort().toString());
		} 
                assert kjt !=  null;
		pvs = pvs.add(new LocationVariable(
				  new ProgramElementName(t.op().name().
							 toString()),
				  kjt));
	    }
	}
    }

    public SetOfProgramVariable getProgramVariables(){
	return pvs;
    }

    public HashMap getTerm2Class(){
	return term2class;
    }

    private SetOfTerm getConstraintsForEqvClass(EquivalenceClass ec){
	IteratorOfTerm it = ec.getMembers().iterator();
	SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
	while(it.hasNext()){
	    SetOfTerm constr = (SetOfTerm) eqvC2constr.get(it.next());
	    if(constr != null){
		result = result.union(constr);
	    }
	}
	return result;
    }

    /**
     * Creates equivalence classes based on the equality formulas (l=r)
     * contained in <code>formulas</code>.
     */
    private void createEquivalenceClassesAndConstraints(){
	term2class = new HashMap();
	IteratorOfTerm it = ante.iterator();
	while(it.hasNext()){
	    EquivalenceClass ec = null;
	    Term t = it.next();
	    collectLocations(t);
	    if(t.op() instanceof Equality && !containsImplicitAttr(t)){
		if(term2class.containsKey(t.sub(0))){
		    ec = (EquivalenceClass) term2class.get(t.sub(0));
		    if(term2class.containsKey(t.sub(1))){
			ec.add((EquivalenceClass) term2class.get(t.sub(1)));
		    }else{
			ec.add(t.sub(1));
		    }
		}else if(term2class.containsKey(t.sub(1))){
		    ec = (EquivalenceClass) term2class.get(t.sub(1));
		    ec.add(t.sub(0));
		}else{
		    ec = new EquivalenceClass(t.sub(0), t.sub(1), serv);
		}
		IteratorOfTerm ecIt = ec.getMembers().iterator();
		while(ecIt.hasNext()){
		    term2class.put(ecIt.next(), ec);  
		}
	    }
	}
	it = succ.iterator();
	while(it.hasNext()){
	    Term t = it.next();
	    collectLocations(t);
	}
    }

    /**
     * Obsolete!
     * Used when it is tried to generate a model without the help of a decision
     * procedure. 
     */
    private void findBounds(){
	IteratorOfTerm it = ante.iterator();
	while(it.hasNext()){
	    Term t = it.next();
	    EquivalenceClass e0, e1;
	    if("lt".equals(t.op().name().toString())){
		e0 = getEqvClass(t.sub(0));
		e1 = getEqvClass(t.sub(1));
		e0.addUpperBound(e1, true);
		e1.addLowerBound(e0, true);
	    }
	}
	it = succ.iterator();
	while(it.hasNext()){
	    Term t = it.next();
	    EquivalenceClass e0, e1;
	    if("lt".equals(t.op().name().toString())){
		e0 = getEqvClass(t.sub(0));
		e1 = getEqvClass(t.sub(1));
		if(e1.addUpperBound(e0, false)){
		    term2class.put(t.sub(0), e1);
		    term2class.put(t.sub(1), e1);
		}else if(e0.addLowerBound(e1, false)){
		    term2class.put(t.sub(0), e0);
		    term2class.put(t.sub(1), e0);
		}
	    }
	}
    }

    private void findDisjointClasses(){
	IteratorOfTerm it = succ.iterator();
	while(it.hasNext()){
	    Term t = it.next();
	    EquivalenceClass e0, e1;
	    if(t.op() instanceof Equality && !containsImplicitAttr(t)){
		e0 = getEqvClass(t.sub(0));
		e1 = getEqvClass(t.sub(1));
		e0.addDisjoint(t.sub(1));
		e1.addDisjoint(t.sub(0));
	    }
	}
    }

    /**
     * Resets the concrete values of all EquivalenceClasses. 
     */
    private void resetAllClasses(LinkedList classes){
	for(int i = 0; i<classes.size(); i++){
	    ((EquivalenceClass) classes.get(i)).resetValue();
	}
    }

    /**
     * Obsolete. Checks whether the current partial model is consistent.
     */
    private boolean consistencyCheck(){
	Iterator it = term2class.values().iterator();
	while(it.hasNext()){
	    EquivalenceClass ec = (EquivalenceClass) it.next();
	    if(ec.isBoolean() && !ec.consistencyCheck(term2class)){
		return false;
	    }
	}
	return true;
    }

    /**
     * Trys to create a model and returns the equivalence classes contained in
     * the partial model.
     */
    public Model[] createModels(){
	DecProdModelGenerator dmg;
	Set intModelSet = new HashSet();
	LinkedList classes = new LinkedList(term2class.values());
	for(int i = classes.size()-1; i>=0; i--){
	    if(//!((EquivalenceClass) classes.get(i)).isInt() &&
		!((EquivalenceClass) classes.get(i)).isBoolean() ||
		((EquivalenceClass) classes.get(i)).getLocations().size()==0){
		classes.remove(i);
	    }
	}
	if(decProdForTestGen == COGENT){
	    dmg = new CogentModelGenerator(
		new CogentTranslation(node.sequent()), serv, 
		term2class, locations);
	    intModelSet = dmg.createModels();
	}
	if(decProdForTestGen == SIMPLIFY /*|| intModelSet.isEmpty()*/){
	    dmg = new SimplifyModelGenerator(node, serv,
		term2class, locations);
	    intModelSet = dmg.createModels();
	}
	Set modelSet = new HashSet();
	Iterator it = intModelSet.iterator();
	while(it.hasNext()){
	    modelSet.addAll(createModelHelp((Model) it.next(), classes));
	}
	Model[] models = new Model[modelSet.size()];
	it = modelSet.iterator();
	int k=0;
	while(it.hasNext()){
	    models[k++] = (Model) it.next();
	}
	// try to merge some models
	int merged = 0;
	Model[] result = new Model[models.length-merged];
	for(int i=0; i<result.length; i++){
	    result[i] = models[i];
	}	
	return result;
    }

    /**
     * Computes values for EquivalenceClasses of type boolean and adds these
     * assignments to the partial model <code>model</code>. 
     */
    private Set createModelHelp(Model model, LinkedList classes){
	HashSet models = new HashSet();
	if(!consistencyCheck()){
	    return models;
	}
	classes = (LinkedList) classes.clone();
	Model m;
	for(int i = classes.size()-1; i>=0; i--){
	    if(((EquivalenceClass) classes.get(i)).
	       hasConcreteValue(term2class) &&
		((EquivalenceClass) classes.get(i)).getLocations().size() > 0){
		model.setValue((EquivalenceClass) classes.remove(i));
	    }
	}
	if(classes.isEmpty()){
	    //model creation successful
	    models.add(model);
	    return models;
	}
	EquivalenceClass ec;
	for(int i = 0; i<classes.size(); i++){
	    ec = (EquivalenceClass) classes.get(i);
	    if(ec.getLocations().size()==0) continue;
	    if(ec.isBoolean()){
		ec.setBoolean(true);
		m = model.copy();
		m.setValue(ec, true);
		models.addAll(createModelHelp(m, classes));
		resetAllClasses(classes);
		ec.setBoolean(false);
		m = model.copy();
		m.setValue(ec, false);
		models.addAll(createModelHelp(m, classes));
		resetAllClasses(classes);
	    }/*else if(ec.isInt()){
		int bound = ec.getMaximalConcreteLowerBound(term2class);
		ec.setInteger(bound);
		m = model.copy();
		m.setValue(ec, bound);
		models.addAll(createModelHelp(m, classes));
		resetAllClasses(classes);
		bound = ec.getMinimalConcreteUpperBound(term2class);
//		if(bound != Integer.MAX_VALUE){
		    ec.setInteger(bound);
		    m = model.copy();
		    m.setValue(ec, bound);
		    models.addAll(createModelHelp(m, classes));
		    resetAllClasses(classes);
//		}
}*/
	}
	return models;
    }

    /**
     * Returns the EquivalenceClasses that contain locations of type int or
     * boolean
     */
    public EquivalenceClass[] getPrimitiveLocationEqvClasses(){
	Object[] oa = (new HashSet(term2class.values())).toArray();
	EquivalenceClass[] temp = new EquivalenceClass[oa.length];
	int l=0;
	for(int i=0; i<oa.length; i++){
	    if(((EquivalenceClass) oa[i]).getLocations().size() > 0 &&
		(((EquivalenceClass) oa[i]).isInt() ||
		 ((EquivalenceClass) oa[i]).isBoolean())){
		temp[l++] = (EquivalenceClass) oa[i];
	    }
	}
	EquivalenceClass[] result = new EquivalenceClass[l];
	for(int i=0; i<l; i++){
	    result[i] = temp[i];
	}
	return result;
    } 

    /**
     * Returns the EquivalenceClasses that contain locations of nonprimitive
     * types.
     */
    public EquivalenceClass[] getNonPrimitiveLocationEqvClasses(){
	Object[] oa = (new HashSet(term2class.values())).toArray();
	EquivalenceClass[] temp = new EquivalenceClass[oa.length];
	int l=0;
	for(int i=0; i<oa.length; i++){
	    if(((EquivalenceClass) oa[i]).getLocations().size() > 0 &&
		(!((EquivalenceClass) oa[i]).isInt() &&
		 !((EquivalenceClass) oa[i]).isBoolean())){
		temp[l++] = (EquivalenceClass) oa[i];
	    }
	}
	EquivalenceClass[] result = new EquivalenceClass[l];
	for(int i=0; i<l; i++){
	    result[i] = temp[i];
	}
	return result;
    } 

    /**
     * Returns the equivalence class of term t. If it doesn't exist yet a new
     * one is created.
     */
    private EquivalenceClass getEqvClass(Term t){
	if(!term2class.containsKey(t)){
	    term2class.put(t, new EquivalenceClass(t, serv));
	}
	return (EquivalenceClass) term2class.get(t);
    }

    public Node getNode() {
        return node;
    }

    public Node getOriginalNode() {
        return originalNode;
    }

}
