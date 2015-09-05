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

package de.uka.ilkd.key.macros;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.settings.ProofSettings;

/**
 * Takes care of providing the whole ProofMacro interface by only making it
 * necessary to implement to most general application methods for a given
 * list of goals and translating the less general versions (firstly for a
 * given node and secondly having neither any goals nor a node). Although
 * all these methods can be redefined by inheritance, this is usually not
 * necessary, unless you know <tt>exactly</tt> what you are doing.
 * The exception is {@link #finishAfterMacro()} for compound macros
 * (see description in {@link ProofMacro#finishAfterMacro()}).
 *
 * @author Michael Kirsten
 */
public abstract class AbstractProofMacro implements ProofMacro {

    private static ImmutableList<Goal> getGoals(Node node) {
        if (node == null) {
            // can happen during initialisation
            return ImmutableSLList.<Goal>nil();
        } else {
            return node.proof().getSubtreeEnabledGoals(node);
        }
    }

    /**
     * {@inheritDoc}
     *
     * By default, proof macros do not support scripts, thus <code>null</code>
     * is returned.
     */
    @Override
    public String getScriptCommandName() {
        return null;
    }

    @Override
    public boolean canApplyTo(Node node,
                              PosInOccurrence posInOcc) {
        return canApplyTo(node.proof(), getGoals(node), posInOcc);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Node node,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException, Exception {
        return applyTo(uic, node.proof(), getGoals(node), posInOcc, listener);
    }

    @Override
    public boolean isApplicableWithoutPosition() {
        return false;
    }

    /**
     * Gets the maximum number of rule applications allowed for a macro. The
     * implementation is the maximum amount of proof steps for automatic mode.
     *
     * @return the maximum number of rule applications allowed for this macro
     */
    final protected int getMaxSteps(Proof proof) {
        final int steps;
        if (proof != null) {
            steps = proof.getSettings()
                         .getStrategySettings().getMaxSteps();
        } else {
            steps = ProofSettings.DEFAULT_SETTINGS
                    .getStrategySettings().getMaxSteps();
        }
        return steps;
    }
}