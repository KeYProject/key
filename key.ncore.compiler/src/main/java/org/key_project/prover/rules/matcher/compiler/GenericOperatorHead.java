/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchIdentityInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

/**
 * The head for an ordinary operator: the operator must be (reference-)identical to the pattern's.
 * This is the language-agnostic default for any operator that has no special matching (i.e. is
 * matched by {@code MatchIdentityInstruction} in the interpreter and by an {@code op() == op} check
 * in the compiler).
 */
public final class GenericOperatorHead implements MatchHead {

    private final Operator op;

    public GenericOperatorHead(Operator op) {
        this.op = op;
    }

    @Override
    public void emit(List<VMInstruction> out) {
        out.add(new MatchIdentityInstruction(op));
        out.add(GotoNextInstruction.INSTANCE);
    }

    @Override
    public MatchProgram compileHeadCheck() {
        final Operator expected = op;
        return (element, mc, services) -> ((Term) element).op() == expected ? mc : null;
    }
}
