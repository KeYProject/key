// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.joinrule.predicateabstraction;

import de.uka.ilkd.key.gui.joinrule.JoinProcedureCompletion;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstraction;

/**
 * Completion class for {@link JoinWithPredicateAbstraction}.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionCompletion extends
        JoinProcedureCompletion<JoinWithPredicateAbstraction> {

    /**
     * TODO: Document.
     */
    public PredicateAbstractionCompletion() {
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.gui.joinrule.JoinProcedureCompletion#complete(de.uka.
     * ilkd.key.rule.join.JoinProcedure, de.uka.ilkd.key.proof.Goal)
     */
    @Override
    public JoinWithPredicateAbstraction complete(
            JoinWithPredicateAbstraction proc, Goal goal) {
        
        
        return null;
    }

}
