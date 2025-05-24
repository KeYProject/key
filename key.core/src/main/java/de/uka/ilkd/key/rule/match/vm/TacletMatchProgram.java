/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayList;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.instructions.*;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableArray;

/**
 * Instances of this class represent programs for matching a term against a given pattern. The
 * programs are specialised for a certain pattern.
 * <br>
 * To create such a program use the static method {@link #createProgram(Term)} and provide as
 * argument the pattern for which you want to get a matcher.
 * <br>
 * The program is executed by invoking
 * {@link TacletMatchProgram#match(Term, MatchConditions, LogicServices)}.
 */
public class TacletMatchProgram {

    /**
     * creates a matcher for the given pattern
     *
     * @param pattern the {@link Term} specifying the pattern
     * @return the specialized matcher for the given pattern
     */
    public static TacletMatchProgram createProgram(Term pattern) {
        ArrayList<MatchInstruction> program = new ArrayList<>();
        createProgram(pattern, program);
        return new TacletMatchProgram(program.toArray(new MatchInstruction[0]));
    }

    /** the skip program (matches anything) */
    public static final TacletMatchProgram EMPTY_PROGRAM =
        new TacletMatchProgram(new MatchInstruction[0]);

    /** the instructions of the program */
    private final MatchInstruction[] instruction;

    /** creates an instance of the matcher consisting of the instruction */
    private TacletMatchProgram(MatchInstruction[] instruction) {
        this.instruction = instruction;
    }

    /**
     * returns the instruction for the specified variable
     *
     * @param op the {@link SchemaVariable} for which to get the instruction
     * @return the instruction for the specified variable
     */
    public static MatchSchemaVariableInstruction getMatchInstructionForSV(
            SchemaVariable op) {
        MatchSchemaVariableInstruction instruction;
        if (op instanceof VariableSV variableSV) {
            instruction = Instruction.matchVariableSV(variableSV);
        } else if (op instanceof ProgramSV programSV) {
            instruction = Instruction.matchProgramSV(programSV);
        } else if (op instanceof OperatorSV) {
            instruction = Instruction.matchNonVariableSV((OperatorSV) op);
        } else {
            throw new IllegalArgumentException(
                "Do not know how to match " + op + " of type " + op.getClass());
        }
        return instruction;
    }



    /**
     * creates a matching program for the given pattern. It appends the necessary match instruction
     * to the given list of instructions
     *
     * @param pattern the Term used as pattern for which to create a matcher
     * @param program the list of {@link MatchInstruction} to which the instructions for matching
     *        {@code pattern} are added.
     */
    private static void createProgram(Term pattern, ArrayList<MatchInstruction> program) {
        final Operator op = pattern.op();

        final ImmutableArray<QuantifiableVariable> boundVars = pattern.boundVars();

        if (!boundVars.isEmpty()) {
            program.add(Instruction.matchAndBindVariables(boundVars));
        }

        if (pattern.hasLabels()) {
            program.add(Instruction.matchTermLabelSV(pattern.getLabels()));
        }

        if (op instanceof SchemaVariable sv) {
            program.add(getMatchInstructionForSV(sv));
            program.add(GotoNextSiblingInstruction.INSTANCE);
        } else {
            program.add(new CheckNodeKindInstruction(Term.class));
            program.add(GotoNextInstruction.INSTANCE);
            if (op instanceof final SortDependingFunction sortDependingFunction) {
                program.add(new CheckNodeKindInstruction(SortDependingFunction.class));
                program.add(new SimilarSortDependingFunctionInstruction(sortDependingFunction));
                program.add(GotoNextInstruction.INSTANCE);
                if (sortDependingFunction.getSortDependingOn() instanceof GenericSort gs) {
                    program.add(new MatchGenericSortInstruction(gs));
                } else {
                    program.add(new MatchIdentityInstruction(sortDependingFunction.getChild(0)));
                }
                program.add(GotoNextSiblingInstruction.INSTANCE);
            } else if (op instanceof ElementaryUpdate elUp) {
                program.add(new CheckNodeKindInstruction(ElementaryUpdate.class));
                program.add(GotoNextInstruction.INSTANCE);
                if (elUp.lhs() instanceof SchemaVariable sv) {
                    program.add(getMatchInstructionForSV(sv));
                    program.add(GotoNextSiblingInstruction.INSTANCE);
                } else if (elUp.lhs() instanceof LocationVariable locVar) {
                    program.add(new MatchIdentityInstruction(locVar));
                    program.add(GotoNextInstruction.INSTANCE);
                }
            } else if (op instanceof Modality mod) {
                program.add(new CheckNodeKindInstruction(Modality.class));
                program.add(GotoNextInstruction.INSTANCE);
                if (mod.kind() instanceof ModalOperatorSV modKindSV) {
                    program.add(Instruction.matchModalOperatorSV(modKindSV));
                } else {
                    program.add(new MatchIdentityInstruction(mod.kind()));
                }
                program.add(GotoNextInstruction.INSTANCE);
                final JavaProgramElement patternPrg = pattern.javaBlock().program();
                program.add(Instruction.matchProgram(patternPrg));
                program.add(GotoNextSiblingInstruction.INSTANCE);
            } else {
                program.add(new MatchIdentityInstruction(op));
                program.add(GotoNextInstruction.INSTANCE);
            }
        }

        if (!boundVars.isEmpty()) {
            for (int i = 0; i < boundVars.size(); i++) {
                program.add(GotoNextSiblingInstruction.INSTANCE);
            }
        }

        for (int i = 0; i < pattern.arity(); i++) {
            createProgram(pattern.sub(i), program);
        }

        if (!boundVars.isEmpty()) {
            program.add(Instruction.unbindVariables(boundVars));
        }

    }


    /**
     * executes the program and tries to match the provided term; additional restrictions are
     * provided via match conditions. The returned conditions are either {@code null} if no match is
     * possible or {@link MatchConditions} which extends the given conditions by additional
     * constraints (e.g., instantiations of schemavariables) such that they describe the found match
     *
     * @param p_toMatch the {@link Term} to match
     * @param p_matchCond the initial {@link MatchConditions} which have to be satisfied in addition
     *        to those generated by this match
     * @param services the {@link Services}
     * @return {@code null} if no match was found or the match result
     */
    public MatchConditions match(Term p_toMatch, MatchConditions p_matchCond,
            LogicServices services) {

        MatchConditions mc = p_matchCond;

        final PoolSyntaxElementCursor navi = PoolSyntaxElementCursor.get(p_toMatch);
        int instrPtr = 0;
        while (mc != null && instrPtr < instruction.length) {
            mc = instruction[instrPtr].match(navi, mc, services);
            instrPtr++;
        }
        navi.release();
        return mc;
    }

}
