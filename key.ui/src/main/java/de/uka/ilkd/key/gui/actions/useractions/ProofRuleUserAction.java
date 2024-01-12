/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions.useractions;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * User action that represents the manual application of a rule.
 * Only used for action history purposes, {@link #apply()} has no functionality.
 *
 * @author Arne Keller
 */
public class ProofRuleUserAction extends ProofModifyingUserAction {
    /**
     * Rule name.
     */
    private final String name;

    /**
     * Construct a new user action of this kind.
     *
     * @param mediator mediator
     * @param proof proof
     * @param goal node the rule was applied on
     * @param name name of the rule
     */
    public ProofRuleUserAction(KeYMediator mediator, Proof proof, Node goal, String name) {
        super(mediator, proof, goal);
        this.name = name;
    }

    @Override
    public String name() {
        return "Apply: " + name;
    }

    @Override
    protected void apply() {
        /* this class just records that a rule application was performed */
    }
}
