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


package de.uka.ilkd.key.ldt;


import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;

/**
 * An "LDT" or "language data type" class corresponds to a standard rule file 
 * shipped with KeY. Usually, this rule file declares a sort (such as "int")
 * and a number of operators.  The LDT class provides a programming interface to 
 * access these entities, and it assists the type converter in handling them.
 */
public abstract class LDT implements Named {
    
    private final Name name;
    
    /** the main sort associated with the LDT */
    private final Sort sort;   
    
    /** the namespace of functions this LDT feels responsible for */
    private final Namespace functions = new Namespace();

    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    protected LDT(Name name, Services services) {
        sort = (Sort) services.getNamespaces().sorts().lookup(name);
	    if (sort == null)
	        throw new RuntimeException("LDT "+name+" not found.\n"+
	                "It seems that there are definitions missing from the .key files.");
        this.name = name;
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    

    /**
     * adds a function to the LDT 
     * @return the added function (for convenience reasons)
     */
    protected final Function addFunction(Function f) {
	functions.add(f);
	return f;
    }
    
    
    /**
     * looks up a function in the namespace and adds it to the LDT 
     * @param funcName the String with the name of the function to look up
     * @return the added function (for convenience reasons)
     */
    protected final Function addFunction(Services services, String funcName) {
	final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function)funcNS.lookup(new Name(funcName));
        if (f == null)
        	throw new RuntimeException("LDT: Function " + funcName + " not found.\n" +
        			"It seems that there are definitions missing from the .key files.");
        return addFunction(f);
    }
    
    
    protected final SortDependingFunction addSortDependingFunction(
	    					Services services, 
	    					String kind) {	
	final SortDependingFunction f 
		= SortDependingFunction.getFirstInstance(new Name(kind), 
							 services);
	assert f != null : "LDT: Sort depending function " 
	                   + kind + " not found";
	addFunction(f);
	return f;
    }

    
    
    /** returns the basic functions of the model
     * @return the basic functions of the model
     */
    protected final Namespace functions() {
	return functions;
    }

    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    

    @Override
    public final Name name() {
	return name;
    }


    @Override
    public final String toString() {
	return "LDT "+name()+" ("+targetSort() + ")";
    }

    
    /** 
     * Returns the sort associated with the LDT.
     */
    public final Sort targetSort() {
	return sort;
    }

    
    public boolean containsFunction(Function op) {
	Named n=functions.lookup(op.name());
	return (n==op);
    }
    
        
    /** returns true if the LDT offers an operation for the given java
     * operator and the logic subterms 
     * @param op the de.uka.ilkd.key.java.expression.Operator to
     * translate
     * @param subs the logic subterms of the java operator
     * @param services the Services
     * @param ec the ExecutionContext in which the expression is evaluated
     * @return  true if the LDT offers an operation for the given java
     * operator and the subterms 
     */
    public abstract boolean isResponsible(
	    		de.uka.ilkd.key.java.expression.Operator op, 
                        Term[] subs, 
                        Services services, 
                        ExecutionContext ec);

    
    /** returns true if the LDT offers an operation for the given
     * binary java operator and the logic subterms 
     * @param op the de.uka.ilkd.key.java.expression.Operator to
     * translate
     * @param left the left subterm of the java operator
     * @param right the right subterm of the java operator
     * @param services the Services
     * @param ec the ExecutionContext in which the expression is evaluated
     * @return  true if the LDT offers an operation for the given java
     * operator and the subterms 
     */
    public abstract boolean isResponsible(
	    		de.uka.ilkd.key.java.expression.Operator op, 
	    		Term left, 
	    		Term right, 
	    		Services services, ExecutionContext ec);

    
    /** returns true if the LDT offers an operation for the given
     * unary java operator and the logic subterms 
     * @param op the de.uka.ilkd.key.java.expression.Operator to
     * translate
     * @param sub the logic subterms of the java operator
     * @param services the Services 
     * @param ec the ExecutionContext in which the expression is evaluated    
     * @return  true if the LDT offers an operation for the given java
     * operator and the subterm
     */
    public abstract boolean isResponsible(
	    		de.uka.ilkd.key.java.expression.Operator op, 
	    		Term sub, 
	    		Services services, 
	    		ExecutionContext ec);


    /** translates a given literal to its logic counterpart 
     * @param lit the Literal to be translated
     * @return the Term that represents the given literal in its logic
     * form
     */ 
    public abstract Term translateLiteral(Literal lit, Services services);

    /** returns the function symbol for the given operation 
     * @return  the function symbol for the given operation 
     */
    public abstract Function getFunctionFor(
	    		de.uka.ilkd.key.java.expression.Operator op, 
	    		Services services, 
	    		ExecutionContext ec);

    public abstract boolean hasLiteralFunction(Function f);

    /** Is called whenever <code>hasLiteralFunction()</code> returns true. */
    public abstract Expression translateTerm(Term t, ExtList children, Services services);
    
    public abstract Type getType(Term t);
}
