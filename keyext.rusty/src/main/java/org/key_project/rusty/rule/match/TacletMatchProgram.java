/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match;

import java.util.ArrayList;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.SVPlace;
import org.key_project.rusty.logic.op.ElementaryUpdate;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.MutRef;
import org.key_project.rusty.logic.op.sv.*;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.match.instructions.Instruction;
import org.key_project.rusty.rule.match.instructions.MatchInstruction;
import org.key_project.rusty.rule.match.instructions.MatchSchemaVariableInstruction;
import org.key_project.util.collection.ImmutableArray;

/**
 * Instances of this class represent programs for matching a term against a given pattern. The
 * programs are specialised for a certain pattern.
 * <br>
 * To create such a program use the static method {@link #createProgram(Term)} and provide as
 * argument the pattern for which you want to get a matcher.
 * <br>
 * The program is executed by invoking
 * {@link TacletMatchProgram#match(Term, MatchConditions, Services)}.
 */
public class TacletMatchProgram {
    /** the skip program (matches anything) */
    public static final TacletMatchProgram EMPTY_PROGRAM =
        new TacletMatchProgram(new MatchInstruction[0]);

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
    public static MatchSchemaVariableInstruction<? extends SchemaVariable> getMatchInstructionForSV(
            SchemaVariable op) {
        MatchSchemaVariableInstruction<? extends SchemaVariable> instruction;

        if (op instanceof FormulaSV formulaSV) {
            instruction = Instruction.matchFormulaSV(formulaSV);
        } else if (op instanceof TermSV termSV) {
            instruction = Instruction.matchTermSV(termSV);
        } else if (op instanceof VariableSV variableSV) {
            instruction = Instruction.matchVariableSV(variableSV);
        } else if (op instanceof ProgramSV programSV) {
            instruction = Instruction.matchProgramSV(programSV);
        } else if (op instanceof UpdateSV updateSV) {
            instruction = Instruction.matchUpdateSV(updateSV);
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

        if (op instanceof SchemaVariable sv) {
            program.add(getMatchInstructionForSV(sv));
        } /*
           * else if (op instanceof SortDependingFunction) {
           * program.add(Instruction.matchSortDependingFunction((SortDependingFunction) op));
           * }
           */ else if (op instanceof ElementaryUpdate eu) {
            program.add(Instruction.matchElementaryUpdate(eu));
        } else if (op instanceof Modality mod) {
            final var kind = mod.kind();
            if (kind instanceof ModalOperatorSV sv) {
                program.add(Instruction.matchModalOperatorSV(sv));
            } else {
                program.add(Instruction.matchModalOperator(mod));
            }
            final RustyProgramElement patternPrg = mod.program().program();
            program.add(Instruction.matchProgram(patternPrg));
        } else if (op instanceof MutRef mr && mr.getPlace() instanceof SVPlace sv) {
            program.add(Instruction.matchPlaceSV(sv));
        } else {
            program.add(Instruction.matchOp(op));
        }

        final ImmutableArray<? extends QuantifiableVariable> boundVars = pattern.boundVars();
        if (!boundVars.isEmpty()) {
            for (int i = 0; i < boundVars.size(); i++) {
                program.add(Instruction.matchAndBindVariable(boundVars.get(i)));
            }
        }

        for (int i = 0; i < pattern.arity(); i++) {
            createProgram(pattern.sub(i), program);
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
    public MatchConditions match(Term p_toMatch, MatchConditions p_matchCond, Services services) {
        MatchConditions mc = p_matchCond;

        final SyntaxElementCursor navi = p_toMatch.getCursor();
        int instrPtr = 0;
        while (mc != null && instrPtr < instruction.length && navi.hasNext()) {
            mc = instruction[instrPtr].match(navi, mc, services);
            instrPtr++;
        }
        // navi.release();
        return mc;
    }
}
