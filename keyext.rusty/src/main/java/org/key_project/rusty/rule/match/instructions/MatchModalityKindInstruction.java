/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElementCursor;
import org.key_project.prover.rules.instantiation.MatchConditions;
import org.key_project.rusty.logic.op.Modality;


/**
 * The match instruction reports a success if the top level operator of the term to be matched is
 * the <strong>same</strong> modality kind like the one for which this instruction has been
 * instantiated
 */
public class MatchModalityKindInstruction implements MatchInstruction {
    private final Modality.RustyModalityKind kind;

    public MatchModalityKindInstruction(Modality.RustyModalityKind kind) {
        super();
        this.kind = kind;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions matchConditions,
            LogicServices services) {
        cursor.goToNext();
        cursor.goToNext();
        var kind = (Modality.RustyModalityKind) cursor.getCurrentNode();
        if (kind != this.kind) {
            return null;
        }
        cursor.goToNext();
        return matchConditions;
    }

}
