/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.logic.Term;
import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.CheckNodeKindInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextSiblingInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

/**
 * Match head for a {@link Modality} {@code \<{ prog }\> post} (the dynamic-logic operator that
 * carries a program): it matches the operator, the modal kind and the program; the post-condition
 * subterm is matched by the enclosing {@link OperatorPlan}. The kind and the program are the
 * modality operator's two syntax children ({@link Modality#kind()},
 * {@link Modality#programBlock()}), so the head itself is language-agnostic: the front-end
 * supplies the kind instruction (a modal-operator schema variable match, or an identity check for
 * a concrete kind) and the {@link ProgramMatchHook} through which the language's program AST is
 * matched.
 */
public final class ModalityHead implements MatchHead {

    /** the pattern's modal kind; kept for {@link #toString} only. */
    private final Modality.Kind patternKind;
    private final MatchInstruction kindInstr;
    private final ProgramMatchHook programHook;

    /**
     * @param patternKind the pattern's modal kind
     * @param kindInstr the instruction matching the modal kind against the source modality's kind
     * @param programHook how the modality's program is matched
     */
    public ModalityHead(Modality.Kind patternKind, MatchInstruction kindInstr,
            ProgramMatchHook programHook) {
        this.patternKind = patternKind;
        this.kindInstr = kindInstr;
        this.programHook = programHook;
    }

    @Override
    public void emit(List<VMInstruction> out) {
        out.add(new CheckNodeKindInstruction(Modality.class));
        out.add(GotoNextInstruction.INSTANCE);
        out.add(kindInstr);
        out.add(GotoNextInstruction.INSTANCE);
        out.add(programHook.programInstruction());
        out.add(GotoNextSiblingInstruction.INSTANCE);
    }

    @Override
    public MatchProgram compileHeadCheck() {
        final MatchInstruction kind = kindInstr;
        final MatchProgram programMatch = programHook.compileProgram();
        return (element, mc, services) -> {
            if (!(((Term) element).op() instanceof Modality m)) {
                return null;
            }
            final MatchResultInfo r = kind.match(m.kind(), mc, services);
            if (r == null) {
                return null;
            }
            return programMatch.match(m.programBlock(), r, services);
        };
    }

    @Override
    public String toString() {
        return "modality(" + patternKind.name() + ", <prog>)";
    }
}
