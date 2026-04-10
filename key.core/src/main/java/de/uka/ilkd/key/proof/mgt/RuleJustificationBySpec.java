/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.Contract;


public record RuleJustificationBySpec(Contract spec) implements RuleJustification {
    /**
     * Contracts for stubs are considered axioms; other contracts not.
     */
    @Override
    public boolean isAxiomJustification() {
        return spec.getTarget() instanceof IProgramMethod
                && !((IProgramMethod) spec.getTarget()).isModel()
                && ((IProgramMethod) spec.getTarget()).getBody() == null;
    }
}
