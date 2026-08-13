/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.List;

import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.matcher.compiler.MatchPlan;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.MatchIdentityInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

public class IdentityMatchPlan implements MatchPlan {
    private final MatchIdentityInstruction instr;

    public IdentityMatchPlan(SyntaxElement se) {
        instr = new MatchIdentityInstruction(se);
    }

    @Override
    public void emit(List<VMInstruction> out) {
        out.add(instr);
    }

    @Override
    public MatchProgram compile() {
        return instr::match;
    }
}
