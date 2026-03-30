/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayList;

import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;

import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;
import org.key_project.util.collection.ImmutableArray;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.*;

/**
 * This class generates a matching program for a given syntax element that can be
 * interpreted by the virtual machine's interpreter
 *
 * @see org.key_project.prover.rules.matcher.vm.VMProgramInterpreter
 */
public class SyntaxElementMatchProgramGenerator {

    /**
     * creates a matcher for the given pattern
     *
     * @param pattern the {@link JTerm} specifying the pattern
     * @return the specialized matcher for the given pattern
     */
    public static VMInstruction[] createProgram(JTerm pattern) {
        ArrayList<VMInstruction> program = new ArrayList<>();
        createProgram(pattern, program);
        return program.toArray(new VMInstruction[0]);
    }

    /**
     * creates a matching program for the given pattern. It appends the necessary match instruction
     * to the given list of instructions
     *
     * @param pattern the {@link JTerm} used as pattern for which to create a matcher
     * @param program the list of {@link MatchInstruction} to which the instructions for matching
     *        {@code pattern} are added.
     */
    private static void createProgram(JTerm pattern, ArrayList<VMInstruction> program) {
        final Operator op = pattern.op();

        final ImmutableArray<QuantifiableVariable> boundVars = pattern.boundVars();

        if (!boundVars.isEmpty()) {
            program.add(matchAndBindVariables(boundVars));
        }

        if (pattern.hasLabels()) {
            program.add(matchTermLabelSV(pattern.getLabels()));
        }

        if (op instanceof SchemaVariable sv) {
            program.add(getMatchInstructionForSV(sv));
            program.add(gotoNextSiblingInstruction());
        } else {
            program.add(getCheckNodeKindInstruction(JTerm.class));
            program.add(gotoNextInstruction());
            switch (op) {
                case ParametricFunctionInstance pfi -> {
                    program.add(getCheckNodeKindInstruction(ParametricFunctionInstance.class));
                    program.add(getSimilarParametricFunctionInstruction(pfi));
                    program.add(gotoNextInstruction());
                    for (int i = 0; i < pfi.getChildCount(); i++) {
                        var arg = (GenericArgument) pfi.getChild(i);
                        if (arg.sort() instanceof GenericSort gs) {
                            program.add(getMatchGenericSortInstruction(gs));
                        } else if (arg.sort() instanceof ParametricSortInstance) {
                            throw new UnsupportedOperationException(
                                "TODO @ DD: Parametric sort in generic args!");
                        } else {
                            program.add(getMatchIdentityInstruction(arg));
                        }
                        program.add(gotoNextInstruction());
                    }
                }
                case final SortDependingFunction sortDependingFunction -> {
                    program.add(getCheckNodeKindInstruction(SortDependingFunction.class));
                    program.add(getSimilarSortDependingFunctionInstruction(sortDependingFunction));
                    program.add(gotoNextInstruction());
                    if (sortDependingFunction.getSortDependingOn() instanceof GenericSort gs) {
                        program.add(getMatchGenericSortInstruction(gs));
                    } else {
                        program.add(getMatchIdentityInstruction(sortDependingFunction.getChild(0)));
                    }
                    program.add(gotoNextInstruction());
                }
                case ElementaryUpdate elUp -> {
                    program.add(getCheckNodeKindInstruction(ElementaryUpdate.class));
                    program.add(gotoNextInstruction());
                    if (elUp.lhs() instanceof SchemaVariable sv) {
                        program.add(getMatchInstructionForSV(sv));
                        program.add(gotoNextSiblingInstruction());
                    } else if (elUp.lhs() instanceof LocationVariable locVar) {
                        program.add(getMatchIdentityInstruction(locVar));
                        program.add(gotoNextInstruction());
                    }
                }
                case Modality mod -> {
                    program.add(getCheckNodeKindInstruction(Modality.class));
                    program.add(gotoNextInstruction());
                    if (mod.kind() instanceof ModalOperatorSV modKindSV) {
                        program.add(matchModalOperatorSV(modKindSV));
                    } else {
                        program.add(getMatchIdentityInstruction(mod.kind()));
                    }
                    program.add(gotoNextInstruction());
                    program.add(matchProgram(pattern.javaBlock().program()));
                    program.add(gotoNextSiblingInstruction());
                }
                default -> {
                    program.add(getMatchIdentityInstruction(op));
                    program.add(gotoNextInstruction());
                }
            }
        }

        if (!boundVars.isEmpty()) {
            for (int i = 0; i < boundVars.size(); i++) {
                program.add(gotoNextSiblingInstruction());
            }
        }

        for (int i = 0; i < pattern.arity(); i++) {
            createProgram(pattern.sub(i), program);
        }

        if (!boundVars.isEmpty()) {
            program.add(unbindVariables(boundVars));
        }
    }
}
