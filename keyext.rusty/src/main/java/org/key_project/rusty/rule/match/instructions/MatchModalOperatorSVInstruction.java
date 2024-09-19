/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.ModalOperatorSV;
import org.key_project.rusty.rule.MatchConditions;

public class MatchModalOperatorSVInstruction implements MatchInstruction {
    private ModalOperatorSV op;

    public MatchModalOperatorSVInstruction(ModalOperatorSV op) {
        this.op = op;
    }

    public MatchConditions match(Modality.RustyModalityKind kind, MatchConditions mc,
            Services services) {
        if (op.getModalities().contains(kind)) {
            return mc.setInstantiations(
                mc.getInstantiations().add(op, kind, services));
        } else {
            return null;
        }
    }

    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions mc,
            Services services) {
        // TODO: is there a better place for this?
        cursor.goToNext();
        cursor.goToNext();
        var node = cursor.getCurrentNode();
        if (!(node instanceof Modality.RustyModalityKind kind))
            return null;
        var result = match(kind, mc, services);
        if (result != null)
            cursor.goToNext();
        return result;
    }
}
