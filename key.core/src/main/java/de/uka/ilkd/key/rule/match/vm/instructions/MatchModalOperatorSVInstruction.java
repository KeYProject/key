/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import java.util.Set;

import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;

public final class MatchModalOperatorSVInstruction implements MatchInstruction {

    private final Set<Modality.JavaModalityKind> modalityKinds;
    private final ModalOperatorSV modalitySV;

    public MatchModalOperatorSVInstruction(ModalOperatorSV mod) {
        this.modalitySV = mod;
        this.modalityKinds = modalitySV.getModalities().toSet();
    }

    @Override
    public MatchConditions match(PoolSyntaxElementCursor cursor,
            MatchConditions mc,
            LogicServices services) {
        if (cursor.getCurrentElement() instanceof Modality.JavaModalityKind kind
                && modalityKinds.contains(kind)) {
            return mc.setInstantiations(
                mc.getInstantiations().add(modalitySV, kind, services));
        } else {
            return null;
        }
    }
}
