/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.settings.ProofSettings;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Takes care of providing the whole ProofMacro interface by only making it necessary to implement
 * to most general application methods for a given list of goals and translating the less general
 * versions (firstly for a given node and secondly having neither any goals nor a node). Although
 * all these methods can be redefined by inheritance, this is usually not necessary, unless you know
 * <tt>exactly</tt> what you are doing. The exception is {@link #finishAfterMacro()} for compound
 * macros (see description in {@link ProofMacro#finishAfterMacro()}).
 *
 * @author Michael Kirsten
 */
public abstract class AbstractProofMacro implements ProofMacro {

    private static ImmutableList<Goal> getGoals(Node node) {
        if (node == null) {
            // can happen during initialisation
            return ImmutableSLList.nil();
        } else {
            return node.proof().getSubtreeEnabledGoals(node);
        }
    }

    /**
     * {@inheritDoc}
     *
     * By default, proof macros do not support scripts, thus <code>null</code> is returned.
     */
    @Override
    public String getScriptCommandName() {
        return null;
    }

    @Override
    public boolean hasParameter(String paramName) {
        return false;
    }

    @Override
    public void setParameter(String paramName, String paramValue) throws IllegalArgumentException {
        throw new IllegalArgumentException(
            String.format("There is no parameter of name %s in macro %s", paramName,
                this.getClass().getSimpleName()));
    }

    @Override
    public void resetParams() {
    }

    @Override
    public boolean canApplyTo(Node node, PosInOccurrence posInOcc) {
        return canApplyTo(node.proof(), getGoals(node), posInOcc);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Node node,
            PosInOccurrence posInOcc, ProverTaskListener listener)
            throws Exception {
        return applyTo(uic, node.proof(), getGoals(node), posInOcc, listener);
    }

    /**
     * Gets the maximum number of rule applications allowed for a macro. The implementation is the
     * maximum amount of proof steps for automatic mode.
     *
     * @return the maximum number of rule applications allowed for this macro
     */
    final protected int getMaxSteps(Proof proof) {
        final int steps;
        if (proof != null) {
            steps = proof.getSettings().getStrategySettings().getMaxSteps();
        } else {
            steps = ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
        }
        return steps;
    }
}
