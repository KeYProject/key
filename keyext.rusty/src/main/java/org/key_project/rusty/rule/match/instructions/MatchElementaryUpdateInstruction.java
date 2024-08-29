/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.ElementaryUpdate;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.match.TacletMatchProgram;

import org.jspecify.annotations.NonNull;

public class MatchElementaryUpdateInstruction extends Instruction<@NonNull ElementaryUpdate> {
    private final MatchOperatorInstruction leftHandSide;

    protected MatchElementaryUpdateInstruction(ElementaryUpdate op) {
        super(op);
        if (op.lhs() instanceof ProgramVariable pv) {
            leftHandSide =
                new MatchOpIdentityInstruction<>(pv);
        } else {
            assert op.lhs() instanceof ProgramSV;
            leftHandSide = (MatchOperatorInstruction) TacletMatchProgram
                    .getMatchInstructionForSV((ProgramSV) op.lhs());
        }
    }

    @Override
    public MatchConditions match(Term instantiationCandidate, MatchConditions matchCond,
            Services services) {
        return match((ElementaryUpdate) instantiationCandidate.op(), matchCond, services);
    }

    public MatchConditions match(ElementaryUpdate instantiationCandidateOp,
            MatchConditions matchCond,
            Services services) {
        if (instantiationCandidateOp != op) {
            matchCond = leftHandSide.match(instantiationCandidateOp.lhs(), matchCond, services);
        }
        return matchCond;
    }

    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions matchConditions,
            Services services) {
        cursor.goToNext();
        var node = cursor.getCurrentNode();
        if (!(node instanceof ElementaryUpdate eu))
            return null;
        final MatchConditions result =
            match(eu, matchConditions, services);
        if (result != null) {
            cursor.gotoNextSibling();
        }
        return result;
    }
}
