// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.simplify;

import de.uka.ilkd.key.unittest.simplify.ast.*;
import de.uka.ilkd.key.unittest.simplify.translation.*;
import de.uka.ilkd.key.unittest.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.parser.simplify.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

import java.io.StringReader;
import java.util.*;

public class OldSimplifyModelGenerator extends DecProdModelGenerator {

    private Services serv;

    private HashMap<String, EquivalenceClass> string2class;

    private HashMap<Term, EquivalenceClass> term2class;

    private HashSet<EquivalenceClass> intClasses;

    private String initialCounterExample;

    /** first element has to be 0. Only positive values at even indices. */
    protected static int[] genericTestValues = new int[] { 0, -1, 1, -10,
	    10, -1000, 1000, -1000000, 1000000, -2000000000, 2000000000 };
    
    /**In the original implementation the value was 1. But some examples are solved at depth 3 and it takes a long time until 3 is reached. */
    public static int iterativeDeepeningStart = 1;

    /** Outputs of Simplify are cached in order to prevent Simplify
     from being called several times with the same formula -> saves execution
     time */
    private HashSet<String> simplifyOutputs;

    private ImmutableList<String> placeHoldersForClasses = ImmutableSLList.<String>nil();

    public static int getModelLimit() {
	return SimplifyModelGenerator.modelLimit;
    }

    public OldSimplifyModelGenerator(DecisionProcedureSimplify dps,
	    Services serv, HashMap<Term, EquivalenceClass> term2class,
	    ImmutableSet<Term> locations) {

	this.serv = serv;
	this.term2class = term2class;

	DecisionProcedureResult res = dps.run(true);
	initialCounterExample = res.getText();
	this.simplifyOutputs = new HashSet<String>();
	string2class = new HashMap<String, EquivalenceClass>();
	Iterator<Term> it = locations.iterator();
	Vector<QuantifiableVariable> v = new Vector<QuantifiableVariable>();
	SimplifyTranslation st = res.getTranslation();
	try {
	    while (it.hasNext()) {
		de.uka.ilkd.key.logic.Term t = it.next();
		String s = st.pretranslate(t, v).toString();
		string2class.put(s, term2class.get(t));
	    }
	} catch (SimplifyException e) {
	    System.err.println(e);
	}
	intClasses = new HashSet<EquivalenceClass>();
	Iterator<EquivalenceClass> itc = term2class.values().iterator();
	int index = initialCounterExample.indexOf("AND") + 4;
	while (itc.hasNext() && index != 3) {
	    EquivalenceClass ec = itc.next();
	    try {
		if (ec.isInt() && ec.getLocations().size() != 0
			&& !intClasses.contains(ec)) {
		    String ph = "(_placeHolder_" + intClasses.size() + ")";
		    string2class.put(ph, ec);
		    placeHoldersForClasses = placeHoldersForClasses.append(ph);
		    intClasses.add(ec);
		    de.uka.ilkd.key.logic.Term loc = ec.getLocations()
			    .iterator().next();
		    String eq = "(EQ " + ph + " " + st.pretranslate(loc, v)
			    + ")\n";
		    initialCounterExample = initialCounterExample.substring(0,
			    index)
			    + eq + initialCounterExample.substring(index);
		}
	    } catch (SimplifyException e) {
		System.err.println(e);
	    }
	}
    }

    public Set<Model> createModels() {
	HashSet<Model> models = new HashSet<Model>();
	int datCount = iterativeDeepeningStart;
	while (models.size() < getModelLimit()
		&& datCount <= genericTestValues.length) {
	    createModels_ProgressNotification1(initialCounterExample,datCount);
	    simplifyOutputs.clear();
	    models.addAll(createModelsHelp(initialCounterExample, new Model(
		    term2class), datCount++, 0));
	}
	return models;
    }
    
    /** Ment to be overwritten by OLDSimplifyMG_GUIInterface*/
    protected void createModels_ProgressNotification1(String initCounterExample, int datCount){ }

    public static final String[] POS = new String[]{"POS0","POS1","POS2","POS3","POS4"};


    /** This method calls itself recursively and tries to create in each recursion step a more concrete
     * model. Firstly inequations ("NEQ") are replaced by "<" then, then "<=" and "<" are replaced
     * by equations.   */
    private Set<Model> createModelsHelp(String counterEx, Model model,
	    int datCount, int recDepth) {
	String counterExOLD = new String(counterEx);
	createModelsHelp_ProgressNotification1(counterExOLD);
	Set<Model> models = new HashSet<Model>();
	if (counterEx.indexOf("Counterexample") == -1
		|| models.size() >= getModelLimit()
		|| terminateAsSoonAsPossible) {
	    return models;
	}
	counterEx = counterEx.replaceAll("_ ", "_");
	counterEx = removeIrrelevantSubformulas(counterEx);
	if (simplifyOutputs.contains(counterEx)) {
	    ModelGenerator.cached++;
	    return models;
	}
	StringReader stream = new StringReader(counterEx);
	SimplifyParser parser = new SimplifyParser(new SimplifyLexer(stream),serv);
	Conjunction c = null;
	try {
	    c = parser.top();
	} catch (Exception e) {
	    String errMsg = e.getMessage()
		    + "\nThe input of the SimplifyParser that reads the output from simplify was (between the \"====\"):\n=====START======\n"
		    + counterEx
		    + "\n=====END=======\nThe original output of simplify before cleanup was:\n=====START======\n"
		    + counterExOLD;
	    throw new RuntimeException(errMsg);
	}
	removeNegativeArrayIndices(c);
	Equation[] eqs = c.getEquations();
	if (eqs.length == c.arity()) {
	    for (int i = 0; i < eqs.length; i++) {
		de.uka.ilkd.key.unittest.simplify.ast.Term ft = eqs[i].sub(0);
		EquivalenceClass ec = getEqvClass(ft);
		if (ec != null && ec.getLocations().size() > 0
			&& eqs[i].sub(1) instanceof NumberTerm) {
		    model.setValue(ec, ((NumberTerm) eqs[i].sub(1)).getValue());
		}
	    }
	    if (model.size() == intClasses.size()) {
		models.add(model);
		createModelsHelp_ProgressNotificationX(POS[0], datCount, recDepth, "model.size() == intClasses.size() == "+model.size());
	    } else {
		//The condition i<1 prevents that PERMUTATIONS of equations are enumerated.
		//Enumeration of equations is done via recursive calls of this method.
		for (int i = 0; i < eqs.length && i < 1; i++) {
		    // set a subterm to an arbitrary value an test if
		    // the system of equations has a unique solution now.
		    for (int j = 0; j < datCount; j++) {
			Equation e = createEquationForSubTerm(eqs[i],
				-genericTestValues[j]);
			if (e != null) {
			    c.add(e);
			    createModelsHelp_ProgressNotificationX(POS[1], datCount, 
				    recDepth, //"createEquationForSubTerm("+eqs[i]+","+genericTestValues[j]+") = " + 
				    e.toString());
			    models.addAll(createModelsHelp(simplify(c), model.copy(), datCount, recDepth+1));
			    if (models.size() >= getModelLimit()) {
				return models;
			    }
			    c.removeLast();
			}
		    }
		}
	    }
	} else {
	    Inequation[] neq = c.getInequations();
	    for (int i = 0; i < neq.length && i < 1; i++) {
//		for (int j = 1; j < datCount; j++) {
//		    c.add(ineqToEq(neq[i], genericTestValues[j]));
//		    createModelsHelp_ProgressNotificationX(POS[4], recDepth,
//			    "ineqToEq("+genericTestValues[j]+", "+neq[i]+")");
//		    models.addAll(createModelsHelp(simplify(c), model.copy(), datCount, recDepth+1));
//		    if (models.size() >= getModelLimit()) {
//			return models;
//		    }
//		    c.removeLast();
//		}
		//gladisch 14.11.2009 
		for (int j = 0; j < 2 && j<datCount; j++) {
		//This loop changes "(NEQ A B)" either to "(< A B)" or to "(< B A)"
		    c.add(ineqToLess(neq[i], j==0));
		    createModelsHelp_ProgressNotificationX(POS[4], datCount,
			    recDepth, "ineqToLess("+(j==0)+", "+neq[i]+")");
		    models.addAll(createModelsHelp(simplify(c), model.copy(), datCount, recDepth+1));
		    if (models.size() >= getModelLimit()) {
			return models;
		    }
		    c.removeLast();
		}
	    }
	    //The following if-cascade prevents that all permutations of "NEQ"-constraints,
	    //"<="-constraints, and "<"-constraints are enumerated. The permutations would be useless.
	    if(c.getInequations().length==0){
		//This branch is entered in a deeper recursion depth of createModelsHelp, when all inequations are replaced
        	    LessEq[] leqs = c.getLessEq();
        	    //Note, only one iteration is considered of the following loop (because of i<1)
        	    //This is to prevent enumeration of permutations of "<=" constraints when the method is called recursively
        	    for (int i = 0; i < leqs.length && i < 1; i++) {
        		for (int j = 0; j < datCount*2; j += 2) {
        		    c.add(lessEqToEq(leqs[i], genericTestValues[j]));
        		    createModelsHelp_ProgressNotificationX(POS[2], datCount, 
        			    recDepth, "lessEqToEq("+genericTestValues[j]+", "+leqs[i]+" ) ");
        		    models.addAll(createModelsHelp(simplify(c), model.copy(), datCount, recDepth+1));
        		    if (models.size() >= getModelLimit()) {
        			return models;
        		    }
        		    c.removeLast();
        		}
        	    }
        	    if(c.getLessEq().length==0){
        		//This branch is entered in a deeper recursion depth of createModelsHelp, when all <= are solved
                	    Less[] les = c.getLess();
                	    //Note, only one iteration is considered of the following loop (because of i<1)
                	    //This is to prevent enumeration of permutations of "<=" constraints when the method is called recursively
                	    for (int i = 0; i < les.length && i < 1; i++) {
                		for (int j = 2; j < 2 + datCount*2; j += 2) {
                		    c.add(lessToEq(les[i], genericTestValues[j]));
                		    createModelsHelp_ProgressNotificationX(POS[3], datCount,
                			    recDepth, "lessToEq("+genericTestValues[j]+", "+les[i]+")");
                		    models.addAll(createModelsHelp(simplify(c), model.copy(), datCount, recDepth+1));
                		    if (models.size() >= getModelLimit()) {
                			return models;
                		    }
                		    c.removeLast();
                		}
                	    }
        	    }
	    }
	}
	return models;
    }
    
    /**To be overwritten by OLDSimplifyMG_GUIInterface */
    protected void createModelsHelp_ProgressNotification1(String counterExOld){   }

    /**To be overwritten by OLDSimplifyMG_GUIInterface 
     * @param iterativeDeepeningDepth TODO
     * @param info TODO*/
    protected void createModelsHelp_ProgressNotificationX(String codePos, int iterativeDeepeningDepth, int recDepth, String info){   }

    private String simplify(Conjunction c) {
	try {
	    return DecisionProcedureSimplify.execute("(NOT " + c.toSimplify()
		    + ")");
	} catch (Exception e) {
	    throw new RuntimeException(e);
	}
    }

    private Equation createEquationForSubTerm(Equation eq, int x) {
	Equation e = null;
	for (int j = 0; j < 2; j++) {
	    if (!(eq.sub(1) instanceof NumberTerm)
		    && !(eq.sub(0) instanceof NumberTerm)) {
		e = createEquationForSubTermHelp(eq, x);
	    } else {
		e = createEquationForSubTermHelp(eq.sub(0), x);
		if (e == null) {
		    e = createEquationForSubTermHelp(eq.sub(1), x);
		}
	    }
	    if (e != null) {
		return e;
	    }
	}
	return e;
    }

    private void removeNegativeArrayIndices(Conjunction c) {
	for (int i = 0; i < c.arity();) {
	    if (containsNegativeIndex(c.sub(i))) {
		c.remove(c.sub(i));
	    } else {
		i++;
	    }
	}
    }

    private boolean containsNegativeIndex(
	    de.uka.ilkd.key.unittest.simplify.ast.Term t) {
	if (t.op().equals("ArrayOp")) {
	    if ((t.sub(1) instanceof NumberTerm)
		    && ((NumberTerm) t.sub(1)).getValue() < 0) {
		return true;
	    }
	}
	for (int i = 0; i < t.arity(); i++) {
	    if (containsNegativeIndex(t.sub(i))) {
		return true;
	    }
	}
	return false;
    }

    private Equation createEquationForSubTermHelp(
	    de.uka.ilkd.key.unittest.simplify.ast.Term t, int x) {
	for (int i = 0; i < t.arity(); i++) {
	    if ((t.sub(i) instanceof FunctionTerm)
		    && (((FunctionTerm) t.sub(i)).isArithmetic() || getEqvClass(t
			    .sub(i)) != null
			    && getEqvClass(t.sub(i)).isInt())) {
		return new Equation(t.sub(i), new NumberTerm(x));
	    }
	    Equation e = createEquationForSubTermHelp(t.sub(i), x);
	    if (e != null) {
		return e;
	    }
	}
	return null;
    }

    private EquivalenceClass getEqvClass(
	    de.uka.ilkd.key.unittest.simplify.ast.Term t) {
	if (t instanceof FunctionTerm) {
	    return string2class.get(t.toString());
	}
	return null;
    }

    /**
     * Removes uninterpreted predicates and extracts the formula provided by Simplify.
     */
    private String removeIrrelevantSubformulas(String s) {
	int index = s.indexOf("(AND");
	index = s.indexOf("(", index + 1);
	String result = "(AND ";
	while (index < s.length() - 1 && index != -1) {
	    String op = s.substring(index + 1, index + 4);
	    if ((op.startsWith("<=") || op.startsWith("<")
		    || op.startsWith("EQ") || op.startsWith("NEQ"))
		    && s.substring(index, s.indexOf("\n", index) + 1).indexOf(
			    "_undef") == -1
		    && s.substring(index, s.indexOf("\n", index) + 1).indexOf(
			    "(null_") == -1
		    && s.substring(index + 4, s.indexOf("\n", index) + 1)
			    .indexOf("<") == -1) {
		result += " " + s.substring(index, s.indexOf("\n", index) + 1);
	    }
	    index = s.indexOf("\n", index);
	    if (index == -1)
		break;
	    index = s.indexOf("(", index + 1);
	}
	result += ")";
	return result;
    }

    private Equation lessEqToEq(LessEq t, int i) {
	Equation eq = new Equation();
	eq.setLeft(plus(t.sub(0), i));
	eq.setRight(t.sub(1));
	return eq;
    }

    /**
     * @param t
     *            term of the form a<b.
     * @return a+i=b
     */
    private Equation lessToEq(Less t, int i) {
	if (i < 0) {
	    i = -i;
	}
	Equation eq = new Equation();
	eq.setLeft(plus(t.sub(0), i));
	eq.setRight(t.sub(1));
	return eq;
    }

    private de.uka.ilkd.key.unittest.simplify.ast.Term plus(
	    de.uka.ilkd.key.unittest.simplify.ast.Term t, int i) {
	if (i == 0) {
	    return t;
	}
	ExtList l = new ExtList();
	l.add(t);
	l.add(new NumberTerm(i));
	return new FunctionTerm(
		de.uka.ilkd.key.unittest.simplify.ast.Function.PLUS, l);
    }

    private Equation ineqToEq(Inequation t, int i) {
	Equation eq = new Equation();
	eq.setLeft(t.sub(0));
	eq.setRight(plus(t.sub(1), i));
	return eq;
    }

    private Less ineqToLess(Inequation t, boolean inverse) {
	Less less = new Less();
	if(!inverse){
        	less.setLeft(t.sub(0));
        	less.setRight(t.sub(1));
	}else{
    		less.setLeft(t.sub(1));
    		less.setRight(t.sub(0));	    
	}
	return less;
    }

}
