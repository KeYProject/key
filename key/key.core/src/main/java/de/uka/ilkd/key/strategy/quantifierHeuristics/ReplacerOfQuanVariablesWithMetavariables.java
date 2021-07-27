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

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableMap;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class is used to create metavariables for every universal variables in 
 * quantified formula <code>allTerm</code> and create constant functions for
 * all existential variables. The variables with new created metavariables or 
 * constant functions are store to a map <code>mapQM</code>.
 */
@Deprecated
class ReplacerOfQuanVariablesWithMetavariables {

    private ReplacerOfQuanVariablesWithMetavariables () {}
    
    public static Substitution createSubstitutionForVars(Term allTerm, TermServices services) {
        ImmutableMap<QuantifiableVariable,Term> res =
            DefaultImmutableMap.<QuantifiableVariable,Term>nilMap();
        Term t = allTerm;
        Operator op = t.op ();
        while ( op instanceof Quantifier ) {
            QuantifiableVariable q =
                t.varsBoundHere ( 0 ).get ( 0 );
            Term m;
            if ( op == Quantifier.ALL ) {
                Metavariable mv = new Metavariable ( ARBITRARY_NAME, q.sort () );
                m = services.getTermBuilder().var ( mv );
            } else {
                Function f = new Function ( ARBITRARY_NAME, q.sort (),
                                            new Sort [0] );
                m = services.getTermBuilder().func ( f );
            }
            res = res.put ( q, m );
            t = t.sub ( 0 );
            op = t.op ();
        }
        return new Substitution ( res );        
    }
    
    private final static Name ARBITRARY_NAME = new Name ( "unifier" );    

}