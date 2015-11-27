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

import java.util.ArrayList;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.gui.joinrule.JoinProcedureCompletion;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstraction;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstractionFactory;

/**
 * Completion class for {@link JoinWithPredicateAbstraction}.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionCompletion extends
        JoinProcedureCompletion<JoinWithPredicateAbstraction> {

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
        AbstractionPredicatesChoiceDialog dialog =
                new AbstractionPredicatesChoiceDialog(goal);

        assert proc instanceof JoinWithPredicateAbstractionFactory :
            "Exptected an procedure of type JoinWithPredicateAbstractionFactory.";

        JoinWithPredicateAbstractionFactory procF =
                (JoinWithPredicateAbstractionFactory) proc;

        dialog.setVisible(true);

        ArrayList<AbstractionPredicate> chosenPreds =
                dialog.getRegisteredPredicates();

        // A null-pointer in the chosen predicates means that
        // the user has pressed the cancel button.
        if (chosenPreds == null) {
            return proc;
        }
        else {
            return procF.instantiate(chosenPreds, dialog.getLatticeType());
        }
    }

}
