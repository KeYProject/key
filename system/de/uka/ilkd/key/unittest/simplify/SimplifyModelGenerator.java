// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.simplify;

import java.io.IOException;
import java.io.StringReader;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.simplify.SimplifyLexer;
import de.uka.ilkd.key.parser.simplify.SimplifyParser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.unittest.DecProdModelGenerator;
import de.uka.ilkd.key.unittest.EquivalenceClass;
import de.uka.ilkd.key.unittest.Model;
import de.uka.ilkd.key.unittest.ModelGenerator;
import de.uka.ilkd.key.unittest.simplify.ast.*;
import de.uka.ilkd.key.util.ExtList;

public class SimplifyModelGenerator implements DecProdModelGenerator{

    private Services serv;
    private HashMap string2class;
    private HashMap term2class;
    private HashSet intClasses;
    private String initialCounterExample;
    // first element has to be 0. Only positive values at even indices.
    public static int modelLimit = 1;
    private static final int[] genericTestValues = 
    new int[]{0, -1, 1 , -10, 10, -1000, 1000, -1000000, 1000000, -2000000000,
	      2000000000};
    // Outputs of Simplify are stored in order to prevent Simplify
    // from being called several times with the same formula -> saves execution
    // time
    private HashSet simplifyOutputs;
    private ListOfString placeHoldersForClasses = SLListOfString.EMPTY_LIST;
    
    
    private static Term toFormula(Sequent s) {
	TermBuilder tb = TermBuilder.DF;
	Term ante = tb.tt();
	for(ConstrainedFormula cf : s.antecedent()) {
	    ante = tb.and(ante, cf.formula());
	}
	Term succ = tb.ff();
	for(ConstrainedFormula cf : s.succedent()) {
	    succ = tb.or(succ, cf.formula());
	}
	return tb.imp(ante, succ);
    }

    public SimplifyModelGenerator(Node node, 
				  Services serv,
				  HashMap term2class,
				  SetOfTerm locations){
	
	this.serv = serv;
	this.term2class = term2class;
	
	SMTSolver simplify = new SimplifySolver();
	
	SMTSolverResult res = SMTSolverResult.NO_IDEA; 
	
	try {
	    res = simplify.run(toFormula(node.sequent()), 60, serv);
	} catch (IOException ioe) {
	    if (serv.getExceptionHandler() != null) {
		serv.getExceptionHandler().reportException(ioe);
	    } else {
		RuntimeException re = new RuntimeException(ioe.getMessage());
		re.initCause(ioe);
		throw re;
	    }	   
	}
	
	initialCounterExample = res.text();
	this.simplifyOutputs = new HashSet();
	string2class = new HashMap();
	IteratorOfTerm it = locations.iterator();
	
	SMTTranslator st = simplify.getTranslator(serv);

	try{
	    while(it.hasNext()){
		de.uka.ilkd.key.logic.Term t = it.next();
		String s = st.translate(t, serv).toString();
		string2class.put(s, term2class.get(t));
	    }
	}catch(IllegalFormulaException e){
	    System.err.println(e);
	}
	intClasses = new HashSet();
	Iterator itc = term2class.values().iterator();
	int index = initialCounterExample.indexOf("AND")+4;
	while(itc.hasNext() && index!=3){
	    EquivalenceClass ec = (EquivalenceClass) itc.next();
	    try{
		if(ec.isInt() && ec.getLocations().size()!=0 && 
		   !intClasses.contains(ec)){
		    String ph = "(_placeHolder_"+intClasses.size()+")";
		    string2class.put(ph, ec);
		    placeHoldersForClasses = placeHoldersForClasses.append(ph);
		    intClasses.add(ec);
		    de.uka.ilkd.key.logic.Term loc = 
			ec.getLocations().iterator().next();
		    String eq = "(EQ "+ph+" "+st.translate(loc,serv)+")\n";
		    initialCounterExample = 
			initialCounterExample.substring(0, index)+eq+
			initialCounterExample.substring(index);
		}
	    }catch(IllegalFormulaException e){
		System.err.println(e);
	    }
	}
    }

    public Set createModels(){
	HashSet models = new HashSet();	
	int datCount = 1;
	while(models.size() < modelLimit && 
	      datCount <= genericTestValues.length){
	    models.addAll(createModelsHelp(initialCounterExample, 
					   new Model(term2class),
					   datCount++));
	    simplifyOutputs.clear();
	}
	return models;
    }

    public Set createModelsHelp(String counterEx, Model model, int datCount){
	Set models = new HashSet();
	if(counterEx.indexOf("Counterexample") == -1 || 
	   models.size() >= modelLimit){
	    return models;
	}
	counterEx = counterEx.replaceAll("_ ", "_");
	counterEx = removeIrrelevantSubformulas(counterEx);
	if(simplifyOutputs.contains(counterEx)){
	    ModelGenerator.cached++;
	    return models;
	}
	StringReader stream = new StringReader(counterEx);
	SimplifyParser parser = 
	    new SimplifyParser(new SimplifyLexer(stream), serv);
	Conjunction c=null;
	try{
	    c = parser.top();
	}catch(Exception e){
	    throw new RuntimeException(e);
	}
	removeNegativeArrayIndices(c);
	Equation[] eqs = c.getEquations();
	if(eqs.length == c.arity()){
	    for(int i = 0; i<eqs.length; i++){
		de.uka.ilkd.key.unittest.simplify.ast.Term ft = eqs[i].sub(0);
		EquivalenceClass ec = getEqvClass(ft);
		if(ec != null && ec.getLocations().size() > 0 &&
		   eqs[i].sub(1) instanceof NumberTerm){
		    model.setValue(
			ec, ((NumberTerm) eqs[i].sub(1)).getValue());
		}
	    }
	    if(model.size()==intClasses.size()){
		models.add(model);
	    }else{
		for(int i = 0; i<eqs.length; i++){
		    //set a subterm to an arbitrary value an test if
		    //the system of equations has a unique solution now.
		    for(int j=0; j<datCount; j++){
			Equation e = createEquationForSubTerm(
			    eqs[i],genericTestValues[j]);
			if(e!=null){
			    c.add(e);
			    models.addAll(createModelsHelp(simplify(c), 
							   model.copy(),
							   datCount));
			    if(models.size() >= modelLimit){
				return models;
			    }
			    c.removeLast();
			}
		    }
		}
	    }
	}else{
	    LessEq[] leqs = c.getLessEq();
	    for(int i = 0; i<leqs.length; i++){
		for(int j=0; j<datCount; j+=2){
		    c.add(lessEqToEq(leqs[i], genericTestValues[j]));
		    models.addAll(createModelsHelp(simplify(c), model.copy(),
						   datCount));
		    if(models.size() >= modelLimit){
			return models;
		    }
		    c.removeLast();
		}
	    }
	    Less[] les = c.getLess();
	    for(int i = 0; i<les.length; i++){
		for(int j=2; j<datCount; j+=2){
		    c.add(lessToEq(les[i], genericTestValues[j]));
		    models.addAll(createModelsHelp(simplify(c), model.copy(),
						   datCount));
		    if(models.size() >= modelLimit){
			return models;
		    }
		    c.removeLast();
		}
	    }
	    Inequation[] neq = c.getInequations();
	    for(int i = 0; i<neq.length; i++){
		for(int j=1; j<datCount; j++){
		    c.add(ineqToEq(neq[i], genericTestValues[j]));
		    models.addAll(createModelsHelp(simplify(c), model.copy(),
						   datCount));
		    if(models.size() >= modelLimit){
			return models;
		    }
		    c.removeLast();
		}
	    }
	}
	return models;
    }
	
    private String simplify(Conjunction c){
	try{
	    return new SimplifySolver().run("(NOT "+c.toSimplify()+")", 60, serv).text();
	}catch(Exception e){
	    throw new RuntimeException(e);
	}
    }

    private Equation createEquationForSubTerm(Equation eq, int x){
	Equation e = null;
	for(int j=0; j<2; j++){
	    if(!(eq.sub(1) instanceof NumberTerm) &&
	       !(eq.sub(0) instanceof NumberTerm)){
		e = createEquationForSubTermHelp(eq, x);
	    }else{
		e = createEquationForSubTermHelp(eq.sub(0), x);
		if(e==null){
		    e = createEquationForSubTermHelp(eq.sub(1), x);
		}
	    }
	    if(e!=null){
		return e;
	    }
	}
	return e;
    }

    private void removeNegativeArrayIndices(Conjunction c){
	for(int i=0; i<c.arity();){
	    if(containsNegativeIndex(c.sub(i))){
		c.remove(c.sub(i));
	    }else{
		i++;
	    }
	}
    }

    private boolean containsNegativeIndex(de.uka.ilkd.key.unittest.
					  simplify.ast.Term t){
	if(t.op().equals("ArrayOp")){
	    if((t.sub(1) instanceof NumberTerm) && 
	       ((NumberTerm) t.sub(1)).getValue()<0){
		return true;
	    }
	}
	for(int i=0; i<t.arity(); i++){
	    if(containsNegativeIndex(t.sub(i))){
		return true;
	    }
	}
	return false;
    }

    private Equation createEquationForSubTermHelp(de.uka.ilkd.key.unittest.
						  simplify.ast.Term t, int x){
	for(int i=0; i<t.arity(); i++){
	    if((t.sub(i) instanceof FunctionTerm) && 
	       (((FunctionTerm) t.sub(i)).isArithmetic() || 
		getEqvClass(t.sub(i)) != null && 
		getEqvClass(t.sub(i)).isInt())){
		return new Equation(t.sub(i), new NumberTerm(x));
	    }
	    Equation e = createEquationForSubTermHelp(t.sub(i), x);
	    if(e != null){
		return e;
	    }
	}
	return null;
    }

    private EquivalenceClass getEqvClass(
	de.uka.ilkd.key.unittest.simplify.ast.Term t){
	if(t instanceof FunctionTerm){
	    return (EquivalenceClass) string2class.get(t.toString());
	}
	return null;
    }

    /**
     * Removes uninterpreted predicatesand extracts the formula provided by
     * Simplify.
     */
    private String removeIrrelevantSubformulas(String s){
	int index = s.indexOf("(AND");
	index = s.indexOf("(", index+1);
	String result = "(AND ";
	while(index < s.length()-1 && index != -1){
	    String op = s.substring(index+1, index+4);
	    if((op.startsWith("<=") || op.startsWith("<") || 
		op.startsWith("EQ") || op.startsWith("NEQ")) &&
	       s.substring(index, s.indexOf("\n", index)+1).indexOf("_undef")
	       == -1 &&
	       s.substring(index, s.indexOf("\n", index)+1).indexOf("(null_")
	       == -1 &&
	       s.substring(index+4, s.indexOf("\n", index)+1).indexOf("<")
	       == -1){
		result+=" "+s.substring(index, s.indexOf("\n", index)+1);
	    }
	    index = s.indexOf("\n", index);
	    if(index==-1) break;
	    index = s.indexOf("(", index+1);
	}
	result += ")";
	return result;
    }

    private Equation lessEqToEq(LessEq t, int i){
	Equation eq = new Equation();
	eq.setLeft(plus(t.sub(0), i));
	eq.setRight(t.sub(1));
	return eq;
    }

    /**
     * @param t term of the form a<b.
     * @return a+i=b  
     */
    private Equation lessToEq(Less t, int i){
	if(i<0){
	    i=-i;
	}
	Equation eq = new Equation();
	eq.setLeft(plus(t.sub(0), i));
	eq.setRight(t.sub(1));
	return eq;
    }

    private de.uka.ilkd.key.unittest.simplify.ast.Term 
    plus(de.uka.ilkd.key.unittest.simplify.ast.Term t, int i){
	if(i==0){
	    return t;
	}
	ExtList l = new ExtList();
	l.add(t);
	l.add(new NumberTerm(i));
	return new FunctionTerm(de.uka.ilkd.key.unittest.simplify.ast.
				Function.PLUS, l);
    }

  
    private Equation ineqToEq(Inequation t, int i){
	Equation eq = new Equation();
	eq.setLeft(t.sub(0));
	eq.setRight(plus(t.sub(1), i));
	return eq;
    }



}
