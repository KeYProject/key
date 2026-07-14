/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.List;

import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.matcher.compiler.MatchHead;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getCheckNodeKindInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchIdentityInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchInstructionForSV;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.gotoNextInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.gotoNextSiblingInstruction;

/**
 * Match head for an {@link ElementaryUpdate} {@code lhs := value}: it matches the operator and the
 * left-hand side; the value subterm is matched by the enclosing
 * {@link org.key_project.prover.rules.matcher.compiler.OperatorPlan}. Mirrors the elementary-update
 * fragments of the hand-written interpreter generator and compiled matcher.
 */
public final class ElementaryUpdateHead implements MatchHead {

    private final MatchInstruction lhsMatcher;
    /** whether the left-hand side is a schema variable (it advances by sibling, not by descent). */
    private final boolean lhsIsSchemaVariable;

    private ElementaryUpdateHead(MatchInstruction lhsMatcher, boolean lhsIsSchemaVariable) {
        this.lhsMatcher = lhsMatcher;
        this.lhsIsSchemaVariable = lhsIsSchemaVariable;
    }

    /**
     * @param elUp the elementary update pattern
     * @return a head for {@code elUp}, or {@code null} if its left-hand side is neither a schema
     *         variable nor a concrete location variable (then the caller falls back)
     */
    public static @Nullable ElementaryUpdateHead of(ElementaryUpdate elUp) {
        if (elUp.lhs() instanceof SchemaVariable sv) {
            return new ElementaryUpdateHead(getMatchInstructionForSV(sv), true);
        } else if (elUp.lhs() instanceof LocationVariable locVar) {
            return new ElementaryUpdateHead(getMatchIdentityInstruction(locVar), false);
        }
        return null;
    }

    @Override
    public void emit(List<VMInstruction> out) {
        out.add(getCheckNodeKindInstruction(ElementaryUpdate.class));
        out.add(gotoNextInstruction());
        out.add(lhsMatcher);
        out.add(lhsIsSchemaVariable ? gotoNextSiblingInstruction() : gotoNextInstruction());
    }

    @Override
    public MatchProgram compileHeadCheck() {
        final MatchInstruction lhs = lhsMatcher;
        return (element, mc,
                services) -> ((Term) element).op() instanceof ElementaryUpdate actualElUp
                        ? lhs.match(actualElUp.lhs(), mc, services)
                        : null;
    }
}
