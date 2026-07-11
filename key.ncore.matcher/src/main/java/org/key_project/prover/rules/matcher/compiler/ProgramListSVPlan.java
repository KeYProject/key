/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

/**
 * A list program schema variable ({@code #slist}, {@code #elist}, ...), which matches a run of
 * consecutive source children rather than exactly one (variable arity). It is never matched on
 * its own: the enclosing plan drives it (see {@link ProgramChildSequence}), so this plan's own
 * {@link #emit} and {@link #compile} are never called and throw. It announces itself through
 * {@link #listSV()}, and it is <em>not interpretable</em> — a run of children cannot be expressed
 * on the interpreter's single-step cursor, so a program containing one keeps the interpreter
 * back-end's own matcher while the compiled back-end handles it. This is the one deliberate point
 * where the two back-ends diverge.
 */
public final class ProgramListSVPlan implements ProgramMatchPlan {

    private final SchemaVariable listSV;

    public ProgramListSVPlan(SchemaVariable listSV) {
        this.listSV = listSV;
    }

    @Override
    public SchemaVariable listSV() {
        return listSV;
    }

    @Override
    public boolean interpretable() {
        return false;
    }

    @Override
    public void emit(List<VMInstruction> out) {
        throw new UnsupportedOperationException(
            "a list SV is not interpretable; the interpreter falls back before emitting");
    }

    @Override
    public MatchProgram compile() {
        throw new UnsupportedOperationException(
            "a list SV is matched by its enclosing element, not standalone");
    }

    @Override
    public String toString() {
        return "listSV(" + listSV + ")";
    }
}
