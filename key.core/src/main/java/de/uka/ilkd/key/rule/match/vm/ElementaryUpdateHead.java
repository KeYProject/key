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
 * Match head for an {@link ElementaryUpdate} {@code lhs := value} (the update operator assigning
 * a value to a program variable): it matches the operator and the left-hand side; the value
 * subterm is matched by the enclosing
 * {@link org.key_project.prover.rules.matcher.compiler.OperatorPlan}.
 */
public final class ElementaryUpdateHead implements MatchHead {

    /**
     * the pattern's update operator; the operator family in {@link #topOperatorDescriptor} and
     * the name in {@link #toString}.
     */
    private final ElementaryUpdate op;
    private final MatchInstruction lhsMatcher;
    /** whether the left-hand side is a schema variable (it advances by sibling, not by descent). */
    private final boolean lhsIsSchemaVariable;

    private ElementaryUpdateHead(ElementaryUpdate op, MatchInstruction lhsMatcher,
            boolean lhsIsSchemaVariable) {
        this.op = op;
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
            return new ElementaryUpdateHead(elUp, getMatchInstructionForSV(sv), true);
        } else if (elUp.lhs() instanceof LocationVariable locVar) {
            return new ElementaryUpdateHead(elUp, getMatchIdentityInstruction(locVar), false);
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

    @Override
    public @Nullable Object topOperatorDescriptor() {
        // with a concrete left-hand side exactly one update operator is accepted (elementary
        // updates are interned per left-hand side); with a schema-variable left-hand side many
        // are, and no single family describes them
        return lhsIsSchemaVariable ? null : op;
    }

    @Override
    public String toString() {
        return "elemUpdate(" + op.name() + ")";
    }
}
