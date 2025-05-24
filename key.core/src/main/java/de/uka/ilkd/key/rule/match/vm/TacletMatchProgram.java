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
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;
import org.key_project.util.collection.ImmutableArray;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.*;

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
        ArrayList<VMInstruction> program = new ArrayList<>();
        createProgram(pattern, program);
        return new TacletMatchProgram(program.toArray(new VMInstruction[0]));
    }

    /** the skip program (matches anything) */
    public static final TacletMatchProgram EMPTY_PROGRAM =
        new TacletMatchProgram(new MatchInstruction[0]);

    /** the instructions of the program */
    private final VMInstruction[] instruction;

    /** creates an instance of the matcher consisting of the instruction */
    private TacletMatchProgram(VMInstruction[] instruction) {
        this.instruction = instruction;
    }


    /**
     * creates a matching program for the given pattern. It appends the necessary match instruction
     * to the given list of instructions
     *
     * @param pattern the Term used as pattern for which to create a matcher
     * @param program the list of {@link MatchInstruction} to which the instructions for matching
     *        {@code pattern} are added.
     */
    private static void createProgram(Term pattern, ArrayList<VMInstruction> program) {
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
            program.add(getCheckNodeKindInstruction(Term.class));
            program.add(gotoNextInstruction());
            if (op instanceof final SortDependingFunction sortDependingFunction) {
                program.add(getCheckNodeKindInstruction(SortDependingFunction.class));
                program.add(getSimilarSortDependingFunctionInstruction(sortDependingFunction));
                program.add(gotoNextInstruction());
                if (sortDependingFunction.getSortDependingOn() instanceof GenericSort gs) {
                    program.add(getMatchGenericSortInstruction(gs));
                } else {
                    program.add(getMatchIdentityInstruction(sortDependingFunction.getChild(0)));
                }
                program.add(gotoNextInstruction());
            } else if (op instanceof ElementaryUpdate elUp) {
                program.add(getCheckNodeKindInstruction(ElementaryUpdate.class));
                program.add(gotoNextInstruction());
                if (elUp.lhs() instanceof SchemaVariable sv) {
                    program.add(getMatchInstructionForSV(sv));
                    program.add(gotoNextSiblingInstruction());
                } else if (elUp.lhs() instanceof LocationVariable locVar) {
                    program.add(getMatchIdentityInstruction(locVar));
                    program.add(gotoNextInstruction());
                }
            } else if (op instanceof Modality mod) {
                program.add(getCheckNodeKindInstruction(Modality.class));
                program.add(gotoNextInstruction());
                if (mod.kind() instanceof ModalOperatorSV modKindSV) {
                    program.add(matchModalOperatorSV(modKindSV));
                } else {
                    program.add(getMatchIdentityInstruction(mod.kind()));
                }
                program.add(gotoNextInstruction());
                final JavaProgramElement patternPrg = pattern.javaBlock().program();
                program.add(matchProgram(patternPrg));
                program.add(gotoNextSiblingInstruction());
            } else {
                program.add(getMatchIdentityInstruction(op));
                program.add(gotoNextInstruction());
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
    public MatchResultInfo match(Term p_toMatch, MatchConditions p_matchCond,
            LogicServices services) {

        MatchResultInfo mc = p_matchCond;

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
