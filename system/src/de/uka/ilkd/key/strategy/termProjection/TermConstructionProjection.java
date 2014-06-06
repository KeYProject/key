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

package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Term projection for constructing a bigger term from a sequence of direct
 * subterms and an operator.
 * 
 * NB: this is a rather restricted version of term construction, one can think
 * of also allowing bound variables, etc to be specified
 */
public class TermConstructionProjection implements ProjectionToTerm {

    private final Operator               op;
    private final ProjectionToTerm[]     subTerms;
    

    private TermConstructionProjection(Operator op, ProjectionToTerm[] subTerms) {
	assert !(op instanceof Modality); //XXX
        this.op = op;
        this.subTerms = subTerms;
        assert op.arity () == subTerms.length;
    }

    public static ProjectionToTerm create(Operator op,
                                          ProjectionToTerm[] subTerms) {
        return new TermConstructionProjection ( op, subTerms );
    }

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Term[] subs = new Term[subTerms.length];
        for ( int i = 0; i != subTerms.length; ++i ) {
            subs[i] = subTerms[i].toTerm ( app, pos, goal );           
        }
        return goal.proof().getServices().getTermFactory().createTerm ( op, subs, null, null );
    }
    
}