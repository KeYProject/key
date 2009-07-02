// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//


package de.uka.ilkd.key.speclang.ocl.translation;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;


class OCLPredicativeCollection {
    
    private static final String VARNAME_PREFIX = "_oclPC";
    private static final TermFactory tf = TermFactory.DEFAULT;
    private static final TermBuilder tb = TermBuilder.DF;
    private static final CreatedAttributeTermFactory createdFactory
            = CreatedAttributeTermFactory.INSTANCE;
    private static final Term falseTerm = tf.createJunctorTerm(Junctor.FALSE);
    private static int varCounter;
    
    private final LogicVariable var;
    private final Term restriction;
    
    /**
     * Creates a collection which contains all values of a sort which satisfy 
     * some restriction. (predicative)
     */
    protected OCLPredicativeCollection(LogicVariable var, 
                         Term restriction) {
        assert restriction.sort() == Sort.FORMULA;
        this.var         = var;
        this.restriction = restriction;
    }
    
    /**
     * Creates an empty collection.
     */
    protected OCLPredicativeCollection() {
        this.var         = createVar(Sort.ANY);
        this.restriction = falseTerm; 
    }
    
    
    /**
     * Creates a collection which contains all values of a sort which are not null.
     */
    protected OCLPredicativeCollection(Sort sort, Services services) {
        this.var         = createVar(sort);
        this.restriction = tb.not(tb.equals(tb.var(this.var), tb.NULL(services)));
    }

    
    /**
     * Creates a collection which contains a single element.
     */
    protected OCLPredicativeCollection(Term element) {
        this.var = createVar(element.sort());
        this.restriction = tf.createEqualityTerm(getVarAsTerm(), element); 
    }
    
    
    /**
     * Creates a collection which contains all integers between a lower and
     * an upper bound (described by terms of sort int).
     */
    protected OCLPredicativeCollection(Term lowerBound, 
                         Term upperBound, 
                         Function leq) {
        this.var = createVar(lowerBound.sort());
        Term lowerTerm = tf.createFunctionTerm(leq, lowerBound, getVarAsTerm());
        Term upperTerm = tf.createFunctionTerm(leq, getVarAsTerm(), upperBound);
        this.restriction = tf.createJunctorTermAndSimplify(Junctor.AND, lowerTerm, upperTerm); 
    }
    
    
    /**
     * Creates a collection which contains all values reachable from a receiver 
     * term by applying an association with multiplicity > 1 (described by a 
     * predicate).
     */
    protected OCLPredicativeCollection(Term recTerm, 
                         Function assocFunc) {
        assert assocFunc.sort() == Sort.FORMULA;
        assert assocFunc.arity() == 2;
        List<LogicVariable> createdVars = new LinkedList<LogicVariable>();
        Term predicateTerm = createPredicateTerm(assocFunc, 
                                                 recTerm, 
                                                 createdVars);
        assert createdVars.size() == 1;
        
        this.var         = createdVars.get(0);
        this.restriction = predicateTerm;
    }
    
    
    private static LogicVariable createVar(Sort sort) {
        return new LogicVariable(new Name(VARNAME_PREFIX + varCounter++), sort);
    }
    
    
    private static Term createPredicateTerm(
                                Function predicate, 
                                Term argTerm, 
                                /*out*/ List<LogicVariable> createdVars) {
        assert predicate.sort() == Sort.FORMULA;
        
        //prepare arguments
        Term[] argTerms = new Term[predicate.arity()];
        for(int i = 0; i < predicate.arity(); i++) {
            Sort argSort = predicate.argSort(i);
            if(argSort.equals(argTerm.sort())) {
                argTerms[i] = argTerm;
            } else {
                LogicVariable lv = createVar(argSort);
                createdVars.add(lv);
                argTerms[i] = tf.createVariableTerm(lv);
            }
        }

        //create and return predicate term
        return tf.createFunctionTerm(predicate, argTerms);
    }
    
    
    private Term replaceVar(LogicVariable lv1, LogicVariable lv2, Term term) {
        Map<LogicVariable, LogicVariable> map = 
            new LinkedHashMap<LogicVariable, LogicVariable>();
        map.put(lv1, lv2);
        OpReplacer or = new OpReplacer(map);
        return or.replace(term);
    }
    
    
    private Term getConvertedRestriction(Services services,
                                         Term additionalRestriction) {
        Term andTerm = tf.createJunctorTermAndSimplify(Junctor.AND, 
                                                       restriction, 
                                                       additionalRestriction);
        return createdFactory.createCreatedNotNullQuantifierTerm(services, 
                                                          Op.EX, 
                                                          var, 
                                                          andTerm);
    }
        
    
    protected Sort getSort() {
        return var.sort();
    }
    
    
    public LogicVariable getVar() {
        return var;
    }
    
    
    public Term getVarAsTerm() {
        return tf.createVariableTerm(var);
    }
    
    
    public Term getRestriction() {
        return restriction;
    }
    
    
    public String toString() {
        return "(all " + var + " with " + restriction + ")";
    }
    
    
    /**
     * Creates a collection which is a subset of this one.
     */
    protected OCLPredicativeCollection narrow(Term additionalRestriction) {
        Term newRestriction = tf.createJunctorTermAndSimplify(Junctor.AND, 
                                                   restriction, 
                                                   additionalRestriction);
        return new OCLPredicativeCollection(var, newRestriction);
    }
    
    
    /**
     * Creates a collection which is the union of this one and another one.
     */
    protected OCLPredicativeCollection union(OCLCollection c) {
        Term cRestriction = replaceVar(c.getPredVar(), var, c.getPredicativeRestriction());
        Term newRestriction = tf.createJunctorTermAndSimplify(Junctor.OR, 
                                                   restriction, 
                                                   cRestriction);
        return new OCLPredicativeCollection(
                var,
                newRestriction);
    }
    

    /**
     * Creates a collection containing all elements reachable from this one 
     * by applying an attribute, a method, an association etc. This "navigation" 
     * is described by a "navigate term", which could e.g. be "var.a" or
     * "var.m()".
     */
    protected OCLPredicativeCollection navigate(Services services, Term navigateTerm) {
        LogicVariable newVar = createVar(navigateTerm.sort());
        Term newVarTerm = tf.createVariableTerm(newVar);
        Term equalTerm = tf.createEqualityTerm(newVarTerm, navigateTerm);
        Term newRestriction = getConvertedRestriction(services, equalTerm);
        
        return new OCLPredicativeCollection(newVar, newRestriction);
    }
    
    
    /**
     * Creates a collection containing all elements reachable from this one
     * by applying an association with multiplicity > 1 (described by a 
     * predicate).
     */
    protected OCLPredicativeCollection navigate(Services services, Function predicate) {
        assert predicate.sort() == Sort.FORMULA;
        assert predicate.arity() == 2;
            
        List<LogicVariable> createdVars = new LinkedList<LogicVariable>();
        Term predicateTerm = createPredicateTerm(predicate, 
                                                 getVarAsTerm(), 
                                                 createdVars);
        assert createdVars.size() == 1;
        LogicVariable newVar = createdVars.get(0);
        
        Term newRestriction = getConvertedRestriction(services, predicateTerm);
        return new OCLPredicativeCollection(newVar, newRestriction);
    }
}
