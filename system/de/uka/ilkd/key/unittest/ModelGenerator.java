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

    private ImmutableList<Term> ante, succ;

    private HashMap<Term, EquivalenceClass> term2class;

    // Maps a location to the set of formulas it occurs in.
    private HashMap<Term, ImmutableSet<Term>> eqvC2constr;

    private Services serv;

    private ImmutableSet<Term> locations = DefaultImmutableSet.<Term>nil();

    private ImmutableSet<ProgramVariable> pvs = DefaultImmutableSet.<ProgramVariable>nil();

    private Node node;

    private Constraint userConstraint;

    private String executionTrace;

    public Node originalNode;

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
     * to the formulas it occurs in.
     */
    private void collectLocations(Term t) {
	if (isLocation(t, serv)) {
	    getEqvClass(t);
	    locations = locations.add(t);
	    ImmutableSet<Term> constr = eqvC2constr.get(t);
	    if (constr == null) {
		constr = DefaultImmutableSet.<Term>nil();
	    }
	    eqvC2constr.put(t, constr.add(t));
	}
	if (!(t.op() instanceof Modality || t.op() instanceof IUpdateOperator || t
		.op() instanceof Quantifier)) {
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
     * Returns the set of locations occuring in node.
     */
    public ImmutableSet<Term> getLocations() {
	return locations;
    }

    /**
     * Collects the program variables occuring in node.
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
		if (t.sort().toString().startsWith("jint")
			|| t.sort().toString().startsWith("jshort")
			|| t.sort().toString().startsWith("jbyte")
			|| t.sort().toString().startsWith("jlong")
			|| t.sort().toString().startsWith("jchar")) {
		    kjt = serv.getJavaInfo().getKeYJavaType(
			    t.sort().toString().substring(1));
		} else {
		    kjt = serv.getJavaInfo()
			    .getKeYJavaType(t.sort().toString());
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

    // private SetOf<Term> getConstraintsForEqvClass(EquivalenceClass ec) {
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
    private void createEquivalenceClassesAndConstraints() {
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
		} else if (term2class.containsKey(t.sub(1))) {
		    ec = term2class.get(t.sub(1));
		    ec.add(t.sub(0));
		} else {
		    ec = new EquivalenceClass(t.sub(0), t.sub(1), serv);
		}
		Iterator<Term> ecIt = ec.getMembers().iterator();
		while (ecIt.hasNext()) {
		    term2class.put(ecIt.next(), ec);
		}
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
    private void findBounds() {
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

    private void findDisjointClasses() {
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
    private void resetAllClasses(LinkedList<EquivalenceClass> classes) {
	for (int i = 0; i < classes.size(); i++) {
	    (classes.get(i)).resetValue();
	}
    }

    /**
     * Obsolete. Checks whether the current partial model is consistent.
     */
    private boolean consistencyCheck() {
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
	DecProdModelGenerator dmg;
	Set<Model> intModelSet = new HashSet<Model>();
	LinkedList<EquivalenceClass> classes = new LinkedList<EquivalenceClass>(
		term2class.values());
	for (int i = classes.size() - 1; i >= 0; i--) {
	    if (// !((EquivalenceClass) classes.get(i)).isInt() &&
	    !classes.get(i).isBoolean()
		    || classes.get(i).getLocations().size() == 0) {
		classes.remove(i);
	    }
	}
	if (decProdForTestGen == COGENT) {
	    dmg = new CogentModelGenerator(
		    new CogentTranslation(node.sequent()), term2class,
		    locations);
	    intModelSet = dmg.createModels();
	}
	if (decProdForTestGen == SIMPLIFY /* || intModelSet.isEmpty() */) {
	    dmg = new SimplifyModelGenerator(node, serv, term2class, locations);
	    intModelSet = dmg.createModels();
	}
	if (decProdForTestGen == OLD_SIMPLIFY /* || intModelSet.isEmpty() */) {
	    dmg = new OldSimplifyModelGenerator(new DecisionProcedureSimplify(
		    node, userConstraint, serv), serv, term2class, locations);
	    intModelSet = dmg.createModels();
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
	return result;
    }

    /**
     * Computes values for EquivalenceClasses of type boolean and adds these
     * assignments to the partial model <code>model</code>.
     */
    private Set<Model> createModelHelp(Model model,
	    LinkedList<EquivalenceClass> classes) {
	HashSet<Model> models = new HashSet<Model>();
	if (!consistencyCheck()) {
	    return models;
	}
	classes = (LinkedList) classes.clone();
	Model m;
	for (int i = classes.size() - 1; i >= 0; i--) {
	    if (classes.get(i).hasConcreteValue(term2class)
		    && classes.get(i).getLocations().size() > 0) {
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
    private EquivalenceClass getEqvClass(Term t) {
	if (!term2class.containsKey(t)) {
	    term2class.put(t, new EquivalenceClass(t, serv));
	}
	return term2class.get(t);
    }

    // public Node getNode() {
    // return node;
    // }

    public Node getOriginalNode() {
	return originalNode;
    }

}
