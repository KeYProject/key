/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.OperatorSV;
import org.key_project.prover.rules.instantiation.IllegalInstantiationException;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * Base of the schema-variable match instructions ({@code MatchVariableSVInstruction},
 * {@code MatchProgramSVInstruction}, {@code MatchNonVariableSVInstruction}, ...): holds the schema
 * variable and provides {@link #addInstantiation}, the common "instantiate or agree" step: a term
 * candidate is checked for rigidness and either recorded as the schema variable's instantiation or
 * compared (modulo renaming) against the instantiation it already has.
 *
 * <p>
 * A candidate is either a term or a program element (an update's left-hand side, for example, is a
 * program variable). The base routes each candidate to the typed method for its kind; a subclass
 * implements {@link #match(JTerm, MatchResultInfo, LogicServices)} and, if its schema-variable
 * kind can stand for program elements, overrides
 * {@link #match(ProgramElement, MatchResultInfo, LogicServices)}.
 */
public abstract class MatchSchemaVariableInstruction implements MatchInstruction {

    protected final @NonNull OperatorSV op;

    protected MatchSchemaVariableInstruction(@NonNull OperatorSV op) {
        this.op = op;
    }

    /**
     * Tries to add the pair <tt>(this,term)</tt> to the match conditions. If successful the
     * resulting conditions are returned, otherwise null. Failure is possible e.g. if this
     * schemavariable has been already matched to a term <tt>t2</tt> which is not unifiable with the
     * given term.
     */
    protected final MatchConditions addInstantiation(JTerm term, MatchResultInfo matchResultInfo,
            LogicServices services) {

        if (op.isRigid() && !term.isRigid()) {
            return null;
        }

        final MatchConditions matchCond = (MatchConditions) matchResultInfo;
        final SVInstantiations inst = matchCond.getInstantiations();

        final JTerm t = inst.getTermInstantiation(op, inst.getExecutionContext(), services);
        if (t != null) {
            if (!RENAMING_TERM_PROPERTY.equalsModThisProperty(t, term)) {
                return null;
            } else {
                return matchCond;
            }
        }

        try {
            return matchCond.setInstantiations(inst.add(op, term, services));
        } catch (IllegalInstantiationException e) {
            return null;
        }
    }

    /**
     * Routes the candidate to the typed match method for its kind. A candidate that is neither a
     * term nor a program element matches no schema variable.
     */
    @Override
    public final @Nullable MatchResultInfo match(SyntaxElement actualElement, MatchResultInfo mc,
            LogicServices services) {
        if (actualElement instanceof JTerm term) {
            return match(term, mc, services);
        }
        if (actualElement instanceof ProgramElement pe) {
            return match(pe, mc, services);
        }
        return null;
    }

    /**
     * Matches the schema variable against a term candidate.
     *
     * @param instantiationCandidate the {@link JTerm} to be matched
     * @param mc the {@link MatchResultInfo} with the constraints accumulated so far
     * @param services the {@link Services}
     * @return the extended {@link MatchResultInfo}, or {@code null} if the schema variable does
     *         not match the term
     */
    protected abstract @Nullable MatchResultInfo match(JTerm instantiationCandidate,
            MatchResultInfo mc, LogicServices services);

    /**
     * Matches the schema variable against a program element. Most schema-variable kinds stand for
     * terms and cannot match a program element, so this default fails; the program schema variable
     * overrides it.
     *
     * @param instantiationCandidate the {@link ProgramElement} to be matched
     * @param mc the {@link MatchResultInfo} with the constraints accumulated so far
     * @param services the {@link Services}
     * @return the extended {@link MatchResultInfo}, or {@code null} if the schema variable does
     *         not match the program element
     */
    public @Nullable MatchResultInfo match(ProgramElement instantiationCandidate,
            MatchResultInfo mc,
            LogicServices services) {
        return null;
    }

    @Override
    public String toString() {
        return "matchSV(" + op.name() + ")";
    }
}
