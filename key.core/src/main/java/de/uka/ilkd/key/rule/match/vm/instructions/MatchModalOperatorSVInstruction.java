/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchModalOperatorSVInstruction implements MatchInstruction {

    private ModalOperatorSV op;

    public MatchModalOperatorSVInstruction(ModalOperatorSV op) {
        this.op = op;
    }

    public MatchConditions match(Term t, MatchConditions mc, Services services) {
        if (t.op() instanceof Modality mod
                && op.getModalities().contains(mod.kind())) {
            return mc.setInstantiations(
                mc.getInstantiations().add(op, mod.<Modality.JavaModalityKind>kind(), services));
        } else {
            return null;
        }
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        return match(termPosition.getCurrentSubterm(), mc, services);
    }

}
