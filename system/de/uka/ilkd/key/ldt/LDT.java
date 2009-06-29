// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.ldt;


import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;


public abstract class LDT {
    
    /** the sort, type and kjt represented by the LDT */
    private final Sort sort;   
    private final Type type;
    private final KeYJavaType kjt;
    
    /** the namespace of functions this LDT feels responsible for */
    private Namespace functions = new Namespace();

    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public LDT(Sort sort, Type type) {
	assert sort != null;
        this.sort = sort;
        this.type = type;
	this.kjt  = new KeYJavaType(type, sort);	
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    

    /**
     * adds a function to the LDT 
     * @return the added function (for convenience reasons)
     */
    protected Function addFunction(Function f) {
	functions.add(f);
	return f;
    }
    
    
    /**
     * looks up a function in the namespace and adds it to the LDT 
     * @param funcNS a Namespace with symbols
     * @param funcName the String with the name of the function to look up
     * @return the added function (for convenience reasons)
     */
    protected Function addFunction(Namespace funcNS, String funcName) {
        final Function f = (Function)funcNS.lookup(new Name(funcName));
        assert f != null : "LDT: Function " + funcName + " not found";
        return addFunction(f);
    }
    
    
    /** returns the basic functions of the model
     * @return the basic functions of the model
     */
    protected Namespace functions() {
	return functions;
    }

    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    

    /** 
     * Returns the sort associated with the LDT.
     */
    public Sort targetSort() {
	return sort;
    }

    
    /** 
     * Returns the Java type associated with the LDT (may be null!).
     */
    public Type javaType() {
	return type;
    }

    
    /** 
     * Returns the KeYJavaType associated with the LDT.
     */
    public KeYJavaType getKeYJavaType() {
	return kjt;
    }
    
    
    public String toString() {
	return "LDT "+name()+" ("+targetSort()+"<->"+javaType()+")";
    }
    
    
    public boolean containsFunction(Function op) {
	Named n=functions.lookup(op.name());
	return (n==op);
    }    
    
    
    public abstract Name name();
    
    
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
     * @param ec the ExecutionContext in which the expression is evaluated    * @param services TODO
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
    public abstract Term translateLiteral(Literal lit);

    /** returns the function symbol for the given operation 
     * @return  the function symbol for the given operation 
     */
    public abstract Function getFunctionFor(
	    		de.uka.ilkd.key.java.expression.Operator op, 
	    		Services serv, 
	    		ExecutionContext ec);

    public abstract boolean hasLiteralFunction(Function f);

    public abstract Expression translateTerm(Term t, ExtList children);

}
