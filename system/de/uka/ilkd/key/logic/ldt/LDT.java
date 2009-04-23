// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic.ldt;

import java.util.HashMap;

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
import de.uka.ilkd.key.rule.SetAsListOfTaclet;
import de.uka.ilkd.key.rule.SetOfTaclet;
import de.uka.ilkd.key.util.ExtList;

/** this class extends the class ADT and is used to represent language
 * datatype models e.g. a model for the java type int, boolean etc.
 * It contains the necessary function symbols, sorts and Taclets. The
 * class TypeConverter needs this class to convert java-program
 * constructs to logic terms.
 */
public abstract class LDT {
    
    /** the ldts name */
    private final Name name;
    
    /** the function namespace */
    private Namespace functions = new Namespace();

    /** the model specific rules */
    private SetOfTaclet rules = SetAsListOfTaclet.EMPTY_SET;
    
    /** the sort represented by the LDT */
    protected final Sort sort;
    
    /** 
     * one LDT may model several program types; this is the list
     * of these types
     */
    protected final Type type;
    
    protected HashMap keyJavaType = new HashMap();

    /**
     * creates a new LDT complete with the target sort of the language
     * datatype, the java datatype, and sorts
     * @param name the name of the language datatype model and the 
     * corresponding sort
     * @param sorts  namespace which contains the target sort
     * @param type the type used in the java program esp. in the AST
     * of the java program
     */
    public LDT(Name name, Namespace sorts, Type type) {
        this.name = name;
        this.sort = (Sort) sorts.lookup(name);
        this.type = type;
	keyJavaType.put(type, new KeYJavaType(type, sort));	
    }   

    /**
     * adds a function to the LDT 
     * @return the added function (for convenience reasons)
     */
    public Function addFunction(Function f) {
	functions.add(f);
	return f;
    }
    
    /**
     * looks up a function in the namespace and add it to the LDT 
     * @param funcNS a Namespace with symbols
     * @param funcName the String with the name of the function to look up
     * @return the added function (for convenience reasons)
     */
    public Function addFunction(Namespace funcNS, String funcName) {
        final Function f = (Function)funcNS.lookup(new Name(funcName));
        if (f==null) {
            throw new RuntimeException("IntegerLDT: Function " + funcName + " not found");
        }
        addFunction(f);
        return f;
    }


    /** returns the sort the java type is mapped to
     * @return  the sort the java type is mapped to
     */
    public Sort targetSort(){
	return sort;
    }

    /** returns the java type the model describes
     * @return the java type the model describes
     */
    public Type javaType() {
	return type;
    }

    /** returns the KeYJavaType for the the given type 
     * @param t the Type for which the coressponding KeYJavaType has to be
     * returned 
     * @return the KeYJavaType the the given type t
     */
    public KeYJavaType getKeYJavaType(Type t) {
	return (KeYJavaType)keyJavaType.get(t);
    }

    /** returns the basic functions of the model
     * @return the basic functions of the model
     */
    public Namespace functions() {
	return functions;
    }

    /** returns the model specific rules 
     * @return the model specific rules 
     */
    public SetOfTaclet rules() {
	return rules;
    }

    /** returns the name of the LDT */
    public Name name() {
        return name;
    }
    
    /** toString */
    public String toString() {
	return "LDT "+name()+" ("+targetSort()+"<->"+javaType()+")";
    }

    /** returns the file ID for the parser */
    public String getFile() {
       return name().toString();
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
    public abstract boolean isResponsible
	(de.uka.ilkd.key.java.expression.Operator op, 
                Term[] subs, Services services, ExecutionContext ec);

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
    public abstract boolean isResponsible
	(de.uka.ilkd.key.java.expression.Operator op, 
                Term left, Term right, Services services, ExecutionContext ec);

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
    public abstract boolean isResponsible
	(de.uka.ilkd.key.java.expression.Operator op, Term sub, 
                Services services, ExecutionContext ec);


    /** translates a given literal to its logic counterpart 
     * @param lit the Literal to be translated
     * @return the Term that represents the given literal in its logic
     * form
     */ 
    public abstract Term translateLiteral(Literal lit);

    /** returns the function symbol for the given operation 
     * @return  the function symbol for the given operation 
     */
    public abstract Function getFunctionFor
	(de.uka.ilkd.key.java.expression.Operator op, Services serv, 
                ExecutionContext ec);

    public boolean containsFunction(Function op) {
	Named n=functions.lookup(op.name());
	return (n==op);
    }

    public abstract boolean hasLiteralFunction(Function f);

    public abstract Expression translateTerm(Term t, ExtList children);

}
