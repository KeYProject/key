// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;


/**
 * Creates an operator schemavariable that matches a given set of operators. 
 * All operators to be matched must have the same arity like this 
 * schema variable.
 */
public class OperatorSV extends SchemaVariableAdapter {
  
    /** the set of operators this sv can match */
    private final Set operators;
    
    /**
     * creates an instance of this schemavariable kind that can match any 
     * operator occuring in the set as long as the arities are the same
     * @param name the Name of the schema variable
     * @param sort the Sort the schema variable shall have
     * @param arity the int with the arity
     * @param set the set of operators to be matched by this schemavariable kind
     * 
     */
    OperatorSV(Name name, Sort sort, 
            int arity, HashSet set) {
        
        super(name, arity, Operator.class, sort, false);
        this.operators = (HashSet) set.clone();
    }
    
    /**
     * creates an instance of this schemavariable kind that can match any 
     * operator occuring in the set as long as the arities are the same as long
     * as it is an instance of the given matching type
     * @param name the Name of the schema variable
     * @param matchingType the Class whose instances (including subtypes) can be matched
     * @param sort the Sort the schema variable shall have
     * @param arity the int with the arity
     * @param set the set of operators to be matched by this schemavariable kind
     * 
     */
    protected OperatorSV(Name name, Class matchingType, Sort sort, 
            int arity, HashSet set) {
        
        super(name, arity, matchingType, sort, false);
        this.operators = (HashSet) set.clone();
    }
    
    
    /**
     * checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the {@link Term} is valid.
     */
    public boolean validTopLevel(Term term){
        if (term.arity() != this.arity()) return false;       
        return true;
    }   

    /**
     * returns true if the schemavariable is an operator sv
     */
    public boolean isOperatorSV() {
        return true;
    }
    
    /**
     * returns an unmodifiacle set of operators this schemavariable can match
     */
    public Set operators() {
        return Collections.unmodifiableSet(operators);
    }
    
    /**
     * (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Operator#match(SVSubstitute, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {        
        
        if (!(subst instanceof Operator)) {
            Debug.out("FAILED. ArithmeticOperatorSC matches only operators " +
                        "(template, orig)",
                    this, subst);
            return null;
        }                
        
        final Operator op = (Operator)subst;
        if (operators.contains(op)) {
            Operator o=(Operator) mc.getInstantiations().getInstantiation(this);
            if (o == null) {
                return mc.
                  setInstantiations(mc.getInstantiations().add(this, op));
            } else {
                if (o != op) {
                    Debug.out("FAILED. Already instantiated with a different operator.");
                    return null;
                }
            }                           
        }
        Debug.out("FAILED. template is a schema operator,"
                +" term is an operator, but not a matching one");
        return null; 
    }
    
    /** toString */
    public String toString() {
        return toString(" (operator sv)");
    }

}
