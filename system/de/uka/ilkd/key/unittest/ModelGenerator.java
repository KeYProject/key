// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.util.*;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.unittest.cogent.CogentModelGenerator;
import de.uka.ilkd.key.unittest.cogent.CogentTranslation;
import de.uka.ilkd.key.unittest.simplify.OldSimplifyModelGenerator;
import de.uka.ilkd.key.unittest.simplify.SimplifyModelGenerator;
import de.uka.ilkd.key.unittest.simplify.translation.DecisionProcedureSimplify;

public class ModelGenerator {

    // debug info
    public static int cached = 0;

    public static final int COGENT = 0;

    public static final int SIMPLIFY = 1;

    public static final int OLD_SIMPLIFY = 2;

    public static int decProdForTestGen = OLD_SIMPLIFY;

    protected ImmutableList<Term> ante, succ;

    protected HashMap<Term, EquivalenceClass> term2class;

    /** Maps a location to the set of formulas it occurs in. */
    protected HashMap<Term, ImmutableSet<Term>> eqvC2constr;

    protected Services serv;

    /**Is initialized by method {@code collectLocations(Term t)} */
    protected ImmutableSet<Term> locations = DefaultImmutableSet.<Term>nil();

    /**Is initialized by method {@code collectProgramVariables}. The data comes from the field {@code locations} */
    protected ImmutableSet<ProgramVariable> pvs = DefaultImmutableSet.<ProgramVariable>nil();

    /**The node for which to generate the counter example  */
    protected Node node;

    protected Constraint userConstraint;

    /**Just information for the user. */
    protected String executionTrace;

    /**Used only by VisualDebugger and for information for the user. It's not required for model generation!
     * originalNode may differ from node. The latter is the path condition and original Node may 
     * be a leaf node where the pathconditions is already combined with the post conditiond */
    protected Node originalNode;
    
    /** required in order to access during model generation dmg.terminateAsSoonAsPossible.
     * Do not set this field directly but use getDecProdModelGenerator() instead*/
    protected 	DecProdModelGenerator dmg;

    protected volatile boolean terminateAsSoonAsPossible=false;

    /**@param node this is the node for which a counter example is generated.
     * @param originalNode this may be a leaf node below {@code node}.
     * @param executionTrace is not required for model generation itself. It is just to provide better information to the user  */
    public ModelGenerator(Services serv, Constraint userConstraint, Node node,
	    String executionTrace, Node originalNode) {
	Iterator<ConstrainedFormula> itc = node.sequent().antecedent()
		.iterator();
	ante = ImmutableSLList.<Term>nil();
	while (itc.hasNext()) {
	    ante = ante.append(itc.next().formula());
	}
	itc = node.sequent().succedent().iterator();
	succ = ImmutableSLList.<Term>nil();
	while (itc.hasNext()) {
	    succ = succ.append(itc.next().formula());
	}
	this.node = node;
	this.originalNode = originalNode;
	this.userConstraint = userConstraint;
	this.serv = serv;
	this.executionTrace = executionTrace;
	eqvC2constr = new HashMap<Term, ImmutableSet<Term>>();
	createEquivalenceClassesAndConstraints();
	findBounds();
	findDisjointClasses();
	collectProgramVariables();
    }

    public static boolean isLocation(Term t, Services serv) {
	OpCollector oc = new OpCollector();
	t.execPostOrder(oc);
	if (oc.contains(Op.NULL)) {
	    return false;
	}
	return t.op() instanceof AttributeOp
		&& checkIndices(t, serv)
		&& !((ProgramVariable) ((AttributeOp) t.op()).attribute())
			.isImplicit() || t.op() instanceof ProgramVariable
		&& !((ProgramVariable) t.op()).isImplicit()
		|| t.op() instanceof ArrayOp && checkIndices(t, serv)
		|| t.op() instanceof RigidFunction && t.arity() == 0
		&& !"#".equals(t.op().name().toString())
		&& !"TRUE".equals(t.op().name().toString())
		&& !"FALSE".equals(t.op().name().toString())
		&& t.op().name().toString().indexOf("undef(") == -1;
    }

    /**
     * Returns the associated ExecutionTrace as a String.
     */
    public String getExecutionTrace() {
	return executionTrace;
    }

    /**
     * Returns true iff no negative array indices are contained in t.
     */
    public static boolean checkIndices(Term t, Services serv) {
	if (t.op() instanceof AttributeOp) {
	    return checkIndices(t.sub(0), serv);
	}
	if (t.op() instanceof ArrayOp) {
	    if (t.sub(1).op().name().toString().equals("Z")) {
		if (AbstractMetaOperator.convertToDecimalString(t.sub(1), serv)
			.startsWith("-")) {
		    return false;
		}
	    }
	    return checkIndices(t.sub(0), serv);
	}
	return true;
    }

    /**
     * Ensures the existence of an EquivalenceClass for each location and logic
     * variable found in <code>t</code> and updates the mapping from this class
     * to the formulas it occurs in, i.e. field {@code locations} is initialized.
     * Formulas below modalities, updates, and quantifiers are ignored
     */
    protected void collectLocations(Term t) {
	if (isLocation(t, serv)) {
	    getEqvClass(t);
	    locations = locations.add(t);
	    ImmutableSet<Term> constr = eqvC2constr.get(t);
	    if (constr == null) {
		constr = DefaultImmutableSet.<Term>nil();
	    }
	    eqvC2constr.put(t, constr.add(t));
	}
	if (!(t.op() instanceof Modality || 
		t.op() instanceof IUpdateOperator || 
		t.op() instanceof Quantifier)) {
	    /*
	     * if(t.op() instanceof IUpdateOperator){ IUpdateOperator uop =
	     * (IUpdateOperator) t.op(); for(int i = 0; i<uop.locationCount();
	     * i++){ collectLocations(uop.value(t, i)); } }
	     */
	    for (int i = 0; i < t.arity(); i++) {
		collectLocations(t.sub(i));
	    }
	}
    }

    public static boolean containsImplicitAttr(Term t) {
	if (t.op() instanceof AttributeOp
		&& ((ProgramVariable) ((AttributeOp) t.op()).attribute())
			.isImplicit() || t.op() instanceof ProgramVariable
		&& ((ProgramVariable) t.op()).isImplicit()) {
	    return true;
	}
	for (int i = 0; i < t.arity(); i++) {
	    if (containsImplicitAttr(t.sub(i))) {
		return true;
	    }
	}
	return false;
    }

    /**
     * Returns the set of locations occurring in node.
     */
    public ImmutableSet<Term> getLocations() {
	return locations;
    }

    /**
     * Collects the program variables occurring in node, or more precisely occurring in {@code locations}. 
     * The result is stored in {@code pvs}.
     */
    public void collectProgramVariables() {
	Iterator<Term> it = locations.iterator();
	while (it.hasNext()) {
	    Term t = it.next();
	    if ((t.op() instanceof ProgramVariable)
		    && !((ProgramVariable) t.op()).isStatic()) {
		pvs = pvs.add((ProgramVariable) t.op());
	    } else if (t.op() instanceof RigidFunction) {
		KeYJavaType kjt;
		String sortName = t.sort().toString(); 
		if (	   sortName.startsWith("jint")
			|| sortName.startsWith("jshort")
			|| sortName.startsWith("jbyte")
			|| sortName.startsWith("jlong")
			|| sortName.startsWith("jchar")) {
		    kjt = serv.getJavaInfo().getKeYJavaType(sortName.substring(1));
		} else {
		    kjt = serv.getJavaInfo().getKeYJavaType(sortName);
		}
		assert kjt != null;
		pvs = pvs.add(new LocationVariable(new ProgramElementName(t
			.op().name().toString()), kjt));
	    }
	}
    }

    public ImmutableSet<ProgramVariable> getProgramVariables() {
	return pvs;
    }

    public HashMap<Term, EquivalenceClass> getTerm2Class() {
	return term2class;
    }

    // protected SetOf<Term> getConstraintsForEqvClass(EquivalenceClass ec) {
    // Iterator<Term> it = ec.getMembers().iterator();
    // SetOf<Term> result = SetAsListOf.<Term>nil();
    // while (it.hasNext()) {
    // SetOf<Term> constr = (SetOfTerm) eqvC2constr.get(it.next());
    // if (constr != null) {
    // result = result.union(constr);
    // }
    // }
    // return result;
    // }

    /**
     * Creates equivalence classes based on the equality formulas (l=r)
     * contained in <code>formulas</code>.
     */
    protected void createEquivalenceClassesAndConstraints() {
	term2class = new HashMap<Term, EquivalenceClass>();
	Iterator<Term> it = ante.iterator();
	while (it.hasNext()) {
	    EquivalenceClass ec = null;
	    Term t = it.next();
	    collectLocations(t);
	    if (t.op() instanceof Equality && !containsImplicitAttr(t)) {
		if (term2class.containsKey(t.sub(0))) {
		    ec = term2class.get(t.sub(0));
		    if (term2class.containsKey(t.sub(1))) {
			ec.add(term2class.get(t.sub(1)));
		    } else {
			ec.add(t.sub(1));
		    }
		    term2class.put(t.sub(1), ec);
		} else if (term2class.containsKey(t.sub(1))) {
		    ec = term2class.get(t.sub(1));
		    ec.add(t.sub(0));
		    term2class.put(t.sub(0), ec);
		} else {
		    ec = new EquivalenceClass(t.sub(0), t.sub(1), serv);
		    term2class.put(t.sub(0), ec);
		    term2class.put(t.sub(1), ec);
		}		
//		Iterator<Term> ecIt = ec.getMembers().iterator();
//		while (ecIt.hasNext()) {
//		    term2class.put(ecIt.next(), ec);
//		}
	    }
	}
	it = succ.iterator();
	while (it.hasNext()) {
	    Term t = it.next();
	    collectLocations(t);
	}
    }

    /**
     * Obsolete! Used when it is tried to generate a model without the help of a
     * decision procedure.
     */
    protected void findBounds() {
	Iterator<Term> it = ante.iterator();
	while (it.hasNext()) {
	    Term t = it.next();
	    EquivalenceClass e0, e1;
	    if ("lt".equals(t.op().name().toString())) {
		e0 = getEqvClass(t.sub(0));
		e1 = getEqvClass(t.sub(1));
		e0.addUpperBound(e1, true);
		e1.addLowerBound(e0, true);
	    }
	    //gladisch: What about leq, geq, gt ?
	}
	it = succ.iterator();
	while (it.hasNext()) {
	    Term t = it.next();
	    EquivalenceClass e0, e1;
	    if ("lt".equals(t.op().name().toString())) {
		e0 = getEqvClass(t.sub(0));
		e1 = getEqvClass(t.sub(1));
		if (e1.addUpperBound(e0, false)) {
		    term2class.put(t.sub(0), e1);
		    term2class.put(t.sub(1), e1);
		} else if (e0.addLowerBound(e1, false)) {
		    term2class.put(t.sub(0), e0);
		    term2class.put(t.sub(1), e0);
		}
	    }
	}
    }

    protected void findDisjointClasses() {
	Iterator<Term> it = succ.iterator();
	while (it.hasNext()) {
	    Term t = it.next();
	    EquivalenceClass e0, e1;
	    if (t.op() instanceof Equality && !containsImplicitAttr(t)) {
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
    protected void resetAllClasses(LinkedList<EquivalenceClass> classes) {
	for (int i = 0; i < classes.size(); i++) {
	    (classes.get(i)).resetValue();
	}
    }

    /**
     * Obsolete. Checks whether the current partial model is consistent.
     */
    protected boolean consistencyCheck() {
	Iterator<EquivalenceClass> it = term2class.values().iterator();
	while (it.hasNext()) {
	    EquivalenceClass ec = it.next();
	    if (ec.isBoolean() && !ec.consistencyCheck(term2class)) {
		return false;
	    }
	}
	return true;
    }

    /**
     * Trys to create a model and returns the equivalence classes contained in
     * the partial model.
     */
    public Model[] createModels() {
	terminateAsSoonAsPossible=false;

	LinkedList<EquivalenceClass> classes = 
	    new LinkedList<EquivalenceClass>(term2class.values());
	createModels_progressNotification0(term2class);

	dmg = getDecProdModelGenerator();
	Set<Model> intModelSet = dmg.createModels();
	createModels_progressNotification1(intModelSet);

	for (int i = classes.size() - 1; i >= 0; i--) {
	    if (// !((EquivalenceClass) classes.get(i)).isInt() &&
	    !classes.get(i).isBoolean()
		    || classes.get(i).getLocations().size() == 0) {
		classes.remove(i);
	    }
	}
	    
	Set<Model> modelSet = new HashSet<Model>();
	Iterator<Model> it = intModelSet.iterator();
	while (it.hasNext()) {
	    modelSet.addAll(createModelHelp(it.next(), classes));
	}
	Model[] models = new Model[modelSet.size()];
	it = modelSet.iterator();
	int k = 0;
	while (it.hasNext()) {
	    models[k++] = it.next();
	}
	// try to merge some models
	int merged = 0;
	Model[] result = new Model[models.length - merged];
	for (int i = 0; i < result.length; i++) {
	    result[i] = models[i];
	}
	createModels_progressNotification2(result);
	dmg = null;
	return result;
    }
    
    /** Overwrites the old value of this.dmg.
     * This method is overwritten in ModelGeneratorGUIInterface.
     * The returned DecProdModelGenerator is initialised with {@code node}, {@code term2class}, and {@code locations}*/
    protected DecProdModelGenerator getDecProdModelGenerator(){
	if (decProdForTestGen == COGENT) {
	    dmg = new CogentModelGenerator(
		    new CogentTranslation(node.sequent()), term2class,
		    locations);
	}else	if (decProdForTestGen == SIMPLIFY /* || intModelSet.isEmpty() */) {
	    dmg = new SimplifyModelGenerator(node, serv, term2class, locations);
	}else 	if (decProdForTestGen == OLD_SIMPLIFY /* || intModelSet.isEmpty() */) {
	    dmg = new OldSimplifyModelGenerator(new DecisionProcedureSimplify(
		    node, userConstraint, serv), serv, term2class, locations);
	}else {
	    dmg=null;
	}
	return dmg;

    }
    
    /**Is meant to be overwritten by subclasses in order to give the user feedback. */
    protected void createModels_progressNotification0(HashMap<Term,EquivalenceClass> term2class){ }

    /**Is meant to be overwritten by subclasses in order to give the user feedback. */
    protected void createModels_progressNotification1(Set<Model> intModelSet){ }

    /**Is meant to be overwritten by subclasses in order to give the user feedback. */
    protected void createModels_progressNotification2(Model[] intModelSet){ }

    /**
     * Computes values for EquivalenceClasses of type boolean and adds these
     * assignments to the partial model <code>model</code>.
     */
    protected Set<Model> createModelHelp(Model model,
	    LinkedList<EquivalenceClass> classes) {
	HashSet<Model> models = new HashSet<Model>();
	if (!consistencyCheck() || terminateAsSoonAsPossible) {
	    return models;
	}
	classes = (LinkedList) classes.clone();
	Model m;
	for (int i = classes.size() - 1; i >= 0; i--) {
	    if (classes.get(i).getLocations().size() > 0
		    && classes.get(i).hasConcreteValue(term2class)
		    ) {
		model.setValue(classes.remove(i));
	    }
	}
	if (classes.isEmpty()) {
	    // model creation successful
	    models.add(model);
	    return models;
	}
	EquivalenceClass ec;
	for (int i = 0; i < classes.size(); i++) {
	    ec = classes.get(i);
	    if (ec.getLocations().size() == 0)
		continue;
	    if (ec.isBoolean()) {
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
	    }/*
	      * else if(ec.isInt()){ int bound =
	      * ec.getMaximalConcreteLowerBound(term2class);
	      * ec.setInteger(bound); m = model.copy(); m.setValue(ec, bound);
	      * models.addAll(createModelHelp(m, classes));
	      * resetAllClasses(classes); bound =
	      * ec.getMinimalConcreteUpperBound(term2class); // if(bound !=
	      * Integer.MAX_VALUE){ ec.setInteger(bound); m = model.copy();
	      * m.setValue(ec, bound); models.addAll(createModelHelp(m,
	      * classes)); resetAllClasses(classes); // } }
	      */
	}
	return models;
    }

    /**
     * Returns the EquivalenceClasses that contain locations of type int or
     * boolean
     */
    public EquivalenceClass[] getPrimitiveLocationEqvClasses() {
	EquivalenceClass[] oa = new EquivalenceClass[term2class.size()];
	term2class.values().toArray(oa);
	EquivalenceClass[] temp = new EquivalenceClass[oa.length];
	int l = 0;
	for (int i = 0; i < oa.length; i++) {
	    if (oa[i].getLocations().size() > 0
		    && (oa[i].isInt() || oa[i].isBoolean())) {
		temp[l++] = oa[i];
	    }
	}
	EquivalenceClass[] result = new EquivalenceClass[l];
	for (int i = 0; i < l; i++) {
	    result[i] = temp[i];
	}
	return result;
    }

    /**
     * Returns the EquivalenceClasses that contain locations of nonprimitive
     * types.
     */
    public EquivalenceClass[] getNonPrimitiveLocationEqvClasses() {
	EquivalenceClass[] oa = new EquivalenceClass[term2class.size()];
	term2class.values().toArray(oa);
	EquivalenceClass[] temp = new EquivalenceClass[oa.length];
	int l = 0;
	for (int i = 0; i < oa.length; i++) {
	    if (oa[i].getLocations().size() > 0
		    && (!oa[i].isInt() && !oa[i].isBoolean())) {
		temp[l++] = oa[i];
	    }
	}
	EquivalenceClass[] result = new EquivalenceClass[l];
	for (int i = 0; i < l; i++) {
	    result[i] = temp[i];
	}
	return result;
    }

    /**
     * Returns the equivalence class of term t. If it doesn't exist yet a new
     * one is created.
     */
    protected EquivalenceClass getEqvClass(Term t) {
	if (!term2class.containsKey(t)) {
	    term2class.put(t, new EquivalenceClass(t, serv));
	}
	return term2class.get(t);
    }

    // public Node getNode() {
    // return node;
    // }
    
    /**Notifies the ModelGenerator and DecProcModelGenerators to stop as soon as possible,
     * even if model generation has not finished yet. */
    public void terminateAsSoonAsPossible(){
	terminateAsSoonAsPossible = true;
	dmg.terminateAsSoonAsPossible = true;
    }
    
    public Node getOriginalNode() {
	return originalNode;
    }

}
