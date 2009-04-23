// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                Universitaet Koblenz-Landau, Germany
//                Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
///
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.MapAsListFromQuantifiableVariableToTerm;
import de.uka.ilkd.key.logic.op.MapFromQuantifiableVariableToTerm;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class is used to create metavariables for every universal variables in 
 * quantified formula <code>allTerm</code> and create constant functions for
 * all existential variables. The variables with new created metavariables or 
 * constant functions are store to a map <code>mapQM</code>.
 */
class ReplacerOfQuanVariablesWithMetavariables {

	final private static TermBuilder tb = TermBuilder.DF;

    private ReplacerOfQuanVariablesWithMetavariables () {}
    
    public static Substitution createSubstitutionForVars(Term allTerm) {
        MapFromQuantifiableVariableToTerm res =
            MapAsListFromQuantifiableVariableToTerm.EMPTY_MAP;
        Term t = allTerm;
        Operator op = t.op ();
        while ( op instanceof Quantifier ) {
            QuantifiableVariable q =
                t.varsBoundHere ( 0 ).getQuantifiableVariable ( 0 );
            Term m;
            if ( op == Op.ALL ) {
                Metavariable mv = new Metavariable ( ARBITRARY_NAME, q.sort () );
                m = tb.func ( mv );
            } else {
                Function f = new RigidFunction ( ARBITRARY_NAME, q.sort (),
                                                 new Sort [0] );
                m = tb.func ( f );
            }
            res = res.put ( q, m );
            t = t.sub ( 0 );
            op = t.op ();
        }
        return new Substitution ( res );        
    }
    
    private final static Name ARBITRARY_NAME = new Name ( "unifier" );    

}
