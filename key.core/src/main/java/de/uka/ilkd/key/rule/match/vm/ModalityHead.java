/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.List;

import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;

import org.key_project.logic.Term;
import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.compiler.MatchHead;
import org.key_project.prover.rules.matcher.compiler.ProgramMatchHook;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getCheckNodeKindInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchIdentityInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.gotoNextInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.gotoNextSiblingInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.matchModalOperatorSV;

/**
 * Match head for a {@link Modality} {@code \<{ prog }\> post}: it matches the operator, the modal
 * kind (a {@link ModalOperatorSV} or a concrete kind by identity) and the Java program (through a
 * {@link ProgramMatchHook}); the post-condition subterm is matched by the enclosing
 * {@link org.key_project.prover.rules.matcher.compiler.OperatorPlan}. The program AST is the second
 * cross-language axis (see {@link ProgramMatchHook}); the kind and skeleton are lifted from the
 * hand-written interpreter generator and compiled matcher.
 */
public final class ModalityHead implements MatchHead {

    private final MatchInstruction kindInstr;
    private final ProgramMatchHook programHook;

    private ModalityHead(MatchInstruction kindInstr, ProgramMatchHook programHook) {
        this.kindInstr = kindInstr;
        this.programHook = programHook;
    }

    /**
     * @param mod the modality pattern
     * @param prog the modality's Java program ({@code pattern.javaBlock().program()})
     * @param programInstructions whether the interpreter side converts the program to VM
     *        instructions
     * @return a head for {@code mod}, or {@code null} if the program cannot be matched by the
     *         framework (then the caller falls back)
     */
    public static @Nullable ModalityHead of(Modality mod, JavaProgramElement prog,
            boolean programInstructions) {
        final JavaProgramMatchHook hook = JavaProgramMatchHook.of(prog, programInstructions);
        if (hook == null) {
            return null;
        }
        final MatchInstruction kindInstr = mod.kind() instanceof ModalOperatorSV sv
                ? matchModalOperatorSV(sv)
                : getMatchIdentityInstruction(mod.kind());
        return new ModalityHead(kindInstr, hook);
    }

    @Override
    public void emit(List<VMInstruction> out) {
        out.add(getCheckNodeKindInstruction(Modality.class));
        out.add(gotoNextInstruction());
        out.add(kindInstr);
        out.add(gotoNextInstruction());
        out.add(programHook.programInstruction());
        out.add(gotoNextSiblingInstruction());
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
            return programMatch.match(((JTerm) element).javaBlock(), r, services);
        };
    }
}
