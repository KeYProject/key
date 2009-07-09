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
//

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.SetAsListOfTerm;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.util.LRUCache;

/**
 * This class describes the relation between different clauses in a CNF.
 * If two clauses have the same existential quantifiable variable, we say
 * they are connected. And this property is transtitive.
 */
class ClausesGraph {

    /**
     * Map from  <code>Term</code>(allTerm) to <code>ClausesGraph</code> 
     */
    private final static Map<Term, ClausesGraph> graphCache = new LRUCache<Term, ClausesGraph> (1000);

    private final SetOfQuantifiableVariable exVars;
    
    /**
     * Map from <code>Term</code> to <code>SetOfTerm</code>
     */
    private final Map<Term, SetOfTerm> connections = new HashMap<Term, SetOfTerm>();
    
    private final SetOfTerm clauses;
    
    static ClausesGraph create(Term quantifiedFormula) {
        ClausesGraph graph = graphCache.get ( quantifiedFormula );
        if ( graph == null ) {
            graph = new ClausesGraph ( quantifiedFormula );
            graphCache.put ( quantifiedFormula, graph );
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

            final IteratorOfTerm forIt = clauses.iterator ();
            while ( forIt.hasNext () ) {
                final Term formula = forIt.next ();
                final SetOfTerm oldConnections = getConnections ( formula );
                final SetOfTerm newConnections =
                    getTransitiveConnections ( oldConnections );

                if ( newConnections.size () > oldConnections.size () ) {
                    changed = true;
                    connections.put ( formula, newConnections );
                }
            }

        } while ( changed );
    }

    private SetOfTerm getTransitiveConnections(SetOfTerm formulas) {
        final IteratorOfTerm termIt = formulas.iterator ();
        while ( termIt.hasNext () )
            formulas = formulas.union ( getConnections ( termIt.next () ) );
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
        final SetOfTerm subFormulas1 = computeClauses ( formula1 );
        final IteratorOfTerm it = computeClauses ( formula0 ).iterator ();
        while ( it.hasNext () ) {
            if ( intersect ( getConnections ( it.next () ),
                             subFormulas1 )                .size () > 0 )
                return true;
        }
        return false;
    }
    
    boolean isFullGraph() {
        final IteratorOfTerm it = clauses.iterator ();
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
    private SetOfTerm getConnections(Term formula) {
        return connections.get ( formula );
    }

    /**
     * initiate connection map.
     * 
     */
    private void buildInitialGraph() {
        final IteratorOfTerm it = clauses.iterator ();
        while ( it.hasNext () ) {
            final Term clause = it.next ();
            connections.put ( clause, directConnections ( clause ) );
        }
    }

    /**
     * 
     * @param formula
     * @return set of term that connect to formula.
     */
    private SetOfTerm directConnections(Term formula) {
        SetOfTerm res = SetAsListOfTerm.EMPTY_SET;
        final IteratorOfTerm it = clauses.iterator ();
        while ( it.hasNext () ) {
            final Term clause = it.next ();
            if ( directlyConnected ( clause, formula ) )
                res = res.add ( clause );
        }
        return res;
    }

    /**
     * 
     * @param set
     * @return ture if set contains one or more exists varaible that are also in
     *         exVars
     */
    private boolean containsExistentialVariables(SetOfQuantifiableVariable set) {
        return intersect ( set, exVars ).size () > 0;
    }

    /**
     * @param formula0
     * @param formula1
     * @return true if formula0 and formula1 have one or more exists varaible
     *         that are the same.
     */
    private boolean directlyConnected(Term formula0, Term formula1) {
        return containsExistentialVariables ( intersect ( formula0.freeVars (),
                                                          formula1.freeVars () ) );
    }

    /**
     * @param formula
     * @return retrun set of terms of all clauses under the formula
     */

    private SetOfTerm computeClauses(Term formula) {
        final Operator op = formula.op ();
        if ( op == Junctor.NOT )
            return computeClauses ( formula.sub ( 0 ) );
        else if ( op == Junctor.AND ) {
            return computeClauses ( formula.sub ( 0 ) )
                   .union ( computeClauses ( formula.sub ( 1 ) ) );
        } else {
            return SetAsListOfTerm.EMPTY_SET.add ( formula );
        }
    }

    /**
     * return the exists variables bound in the top level of 
     * a given cnf formula. 
     */
    private SetOfQuantifiableVariable existentialVars(Term formula) {
        final Operator op = formula.op ();
        if ( op == Quantifier.ALL ) return existentialVars ( formula.sub ( 0 ) );
        if ( op == Quantifier.EX )
            return
                existentialVars ( formula.sub ( 0 ) )
                .add ( formula.varsBoundHere ( 0 ).lastQuantifiableVariable () );
        return SetAsListOfQuantifiableVariable.EMPTY_SET;
    }

    /**
     * @return a set of quantifiableVariable which are belonged to 
     *          both set0 and set1 have
     */
    private SetOfQuantifiableVariable intersect(SetOfQuantifiableVariable set0,
                                                SetOfQuantifiableVariable set1) {
        return TriggerUtils.intersect ( set0, set1 );
    }
    
    
    /**
     * 
     * @param set0
     * @param set1
     * @return a set of terms which are belonged to both set0 and set1.
     */
    private SetOfTerm intersect(SetOfTerm set0, SetOfTerm set1) {
        SetOfTerm res = SetAsListOfTerm.EMPTY_SET;
        if ( set0 == null || set1 == null ) return res;
        final IteratorOfTerm it = set0.iterator ();
        while ( it.hasNext () ) {
            final Term el = it.next ();
            if ( set1.contains ( el ) ) res = res.add ( el );
        }
        return res;
    }
   
}

