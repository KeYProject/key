// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;

/**
 * This class describes the relation between different clauses in a CNF.
 * If two clauses have the same existential quantifiable variable, we say
 * they are connected. And this property is transitive.
 */
public class ClausesGraph {
    private final ImmutableSet<QuantifiableVariable> exVars;
    
    /**
     * Map from <code>Term</code> to <code>ImmutableSet<Term></code>
     */
    private final Map<Term, ImmutableSet<Term>> connections = new LinkedHashMap<Term, ImmutableSet<Term>>();
    
    private final ImmutableSet<Term> clauses;
    
    static ClausesGraph create(Term quantifiedFormula, ServiceCaches caches) {
        ClausesGraph graph = caches.getGraphCache().get ( quantifiedFormula );
        if ( graph == null ) {
            graph = new ClausesGraph ( quantifiedFormula );
            caches.getGraphCache().put ( quantifiedFormula, graph );
        }
        return graph;
    }

    private ClausesGraph(Term quantifiedFormula) {
        exVars = existentialVars ( quantifiedFormula );
        clauses = computeClauses ( TriggerUtils.discardQuantifiers ( quantifiedFormula ) );
        buildInitialGraph ();
        buildFixedPoint ();
    }

    private void buildFixedPoint() {
        boolean changed;
        do {
            changed = false;

            for (Term clause : clauses) {
                final Term formula = clause;
                final ImmutableSet<Term> oldConnections = getConnections(formula);
                final ImmutableSet<Term> newConnections =
                        getTransitiveConnections(oldConnections);

                if (newConnections.size() > oldConnections.size()) {
                    changed = true;
                    connections.put(formula, newConnections);
                }
            }

        } while ( changed );
    }

    private ImmutableSet<Term> getTransitiveConnections(ImmutableSet<Term> formulas) {
        for (Term formula : formulas) formulas = formulas.union(getConnections(formula));
        return formulas;
    }

    /**
     * 
     * @param formula0
     * @param formula1
     * @return ture if clause of formula0 and clause of formula1 
     *         are connected.
     */
    boolean connected(Term formula0, Term formula1) {
        final ImmutableSet<Term> subFormulas1 = computeClauses ( formula1 );
        for (Term term : computeClauses(formula0)) {
            if (intersect(getConnections(term),
                    subFormulas1).size() > 0)
                return true;
        }
        return false;
    }
    
    boolean isFullGraph() {
        final Iterator<Term> it = clauses.iterator ();
        if ( it.hasNext () ) {
            if ( getConnections ( it.next () ).size () < clauses.size () )
                return false;
        }
        return true;
    }
 
 
    /**
     * @param formula
     * @return set of terms that connect to the formula.
     */
    private ImmutableSet<Term> getConnections(Term formula) {
        return connections.get ( formula );
    }

    /**
     * initiate connection map.
     * 
     */
    private void buildInitialGraph() {
        for (Term clause1 : clauses) {
            final Term clause = clause1;
            connections.put(clause, directConnections(clause));
        }
    }

    /**
     * 
     * @param formula
     * @return set of term that connect to formula.
     */
    private ImmutableSet<Term> directConnections(Term formula) {
        ImmutableSet<Term> res = DefaultImmutableSet.<Term>nil();
        for (Term clause1 : clauses) {
            final Term clause = clause1;
            if (directlyConnected(clause, formula))
                res = res.add(clause);
        }
        return res;
    }

    /**
     * 
     * @param set
     * @return ture if set contains one or more exists varaible that are also in
     *         exVars
     */
    private boolean containsExistentialVariables(ImmutableSet<QuantifiableVariable> set) {
        return intersectQV ( set, exVars ).size () > 0;
    }

    /**
     * @param formula0
     * @param formula1
     * @return true if formula0 and formula1 have one or more exists varaible
     *         that are the same.
     */
    private boolean directlyConnected(Term formula0, Term formula1) {
        return containsExistentialVariables ( intersectQV ( formula0.freeVars (),
                                                            formula1.freeVars () ) );
    }

    /**
     * @param formula
     * @return retrun set of terms of all clauses under the formula
     */

    private ImmutableSet<Term> computeClauses(Term formula) {
        final Operator op = formula.op ();
        if ( op == Junctor.NOT )
            return computeClauses ( formula.sub ( 0 ) );
        else if ( op == Junctor.AND ) {
            return computeClauses ( formula.sub ( 0 ) )
                   .union ( computeClauses ( formula.sub ( 1 ) ) );
        } else {
            return DefaultImmutableSet.<Term>nil().add ( formula );
        }
    }

    /**
     * return the exists variables bound in the top level of 
     * a given cnf formula. 
     */
    private ImmutableSet<QuantifiableVariable> existentialVars(Term formula) {
        final Operator op = formula.op ();
        if ( op == Quantifier.ALL ) return existentialVars ( formula.sub ( 0 ) );
        if ( op == Quantifier.EX )
            return
                existentialVars ( formula.sub ( 0 ) )
                .add ( formula.varsBoundHere ( 0 ).last () );
        return DefaultImmutableSet.<QuantifiableVariable>nil();
    }

    /**
     * @return a set of quantifiableVariable which are belonged to 
     *          both set0 and set1 have
     */
    private ImmutableSet<QuantifiableVariable> intersectQV(ImmutableSet<QuantifiableVariable> set0,
                                                ImmutableSet<QuantifiableVariable> set1) {
        return TriggerUtils.intersect ( set0, set1 );
    }
    
    
    /**
     * 
     * @param set0
     * @param set1
     * @return a set of terms which are belonged to both set0 and set1.
     */
    private ImmutableSet<Term> intersect(ImmutableSet<Term> set0, ImmutableSet<Term> set1) {
        ImmutableSet<Term> res = DefaultImmutableSet.<Term>nil();
        if ( set0 == null || set1 == null ) return res;
        for (Term aSet0 : set0) {
            final Term el = aSet0;
            if (set1.contains(el)) res = res.add(el);
        }
        return res;
    }
   
}