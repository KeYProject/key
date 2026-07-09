/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextSiblingInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

/**
 * Plan for a (sub)pattern that is a schema variable: it matches the whole element via the provided
 * schema-variable {@link MatchInstruction} (which the front-end supplies, since schema-variable
 * kinds are language-specific).
 *
 * <p>
 * Language-agnostic counterpart of the schema-variable branch of the hand-written matchers: the
 * interpreter emission is {@code matchSV + gotoNextSibling}, the compiled emission applies the
 * schema-variable instruction directly.
 *
 * <p>
 * A schema-variable pattern never carries bound variables (they attach to binder operators, whose
 * terms are matched by {@link OperatorPlan}); a front-end encountering that shape does not build a
 * plan for it.
 */
public final class SchemaVarPlan implements MatchPlan {

    private final MatchInstruction schemaVarInstruction;

    public SchemaVarPlan(MatchInstruction schemaVarInstruction) {
        this.schemaVarInstruction = schemaVarInstruction;
    }

    @Override
    public void emit(List<VMInstruction> out) {
        out.add(schemaVarInstruction);
        out.add(GotoNextSiblingInstruction.INSTANCE);
    }

    @Override
    public MatchProgram compile() {
        return schemaVarInstruction::match;
    }

    @Override
    public String toString() {
        return "sv(" + schemaVarInstruction + ")";
    }
}
