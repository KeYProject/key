/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
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
        final Operator instantiationCandidateOp = instantiationCandidate.op();
        if (instantiationCandidateOp != op) {
            if (instantiationCandidateOp instanceof ElementaryUpdate instElUpdate) {
                matchCond = leftHandSide.match(instElUpdate.lhs(), matchCond, services);
            } else {
                matchCond = null;
            }
        }
        return matchCond;
    }

    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions matchConditions,
            Services services) {
        final MatchConditions result =
            match((Term) cursor.getCurrentNode(), matchConditions, services);
        if (result != null) {
            cursor.goToNext();
        }
        return result;
    }
}
