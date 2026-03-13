/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.rules.instantiation.AssumesMatchResult;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Defines the interface for matching terms against the pattern (find) part of a taclet,
 * handling schema variable instantiations and checking variable conditions.
 */
public interface TacletMatcher {

    /**
     * Attempts to match the given term against the taclet's "find" term.
     * <p>
     * If the taclet has no "find" term, or if matching fails, this method returns {@code null}.
     *
     * @param term the {@link Term} to be matched against the taclet's "find" expression
     * @param matchCond the current {@link MatchResultInfo} including partial instantiations
     * @param services the {@link LogicServices} providing contextual information
     * @return the updated match result (possibly with added schema variable instantiations) on
     *         success, or {@code null} if no match is found
     */
    @Nullable
    MatchResultInfo matchFind(@NonNull Term term,
            @NonNull MatchResultInfo matchCond,
            @NonNull LogicServices services);

    /**
     * Checks whether a schema variable can be instantiated with the given candidate term,
     * under the provided match conditions.
     *
     * @param var the {@link SchemaVariable} to instantiate
     * @param instantiationCandidate the candidate instantiation for {@code var}
     * @param matchCond the current {@link MatchResultInfo} representing the current match status
     * @param services the {@link LogicServices} providing contextual information
     * @return the updated match result if instantiation is valid, or {@code null} otherwise
     */
    @Nullable
    MatchResultInfo checkVariableConditions(
            org.key_project.logic.op.sv.@Nullable SchemaVariable var,
            @Nullable SyntaxElement instantiationCandidate, @Nullable MatchResultInfo matchCond,
            @NonNull LogicServices services);

    /**
     * Checks the given match result against the taclet's variable conditions.
     * <p>
     * Returns an updated match result if all conditions are satisfied. If not, or if
     * {@code matchResultInfo} is {@code null}, the method returns {@code null}.
     *
     * @param matchResultInfo the match result to validate
     * @param services the {@link LogicServices} providing contextual information
     * @return the validated and potentially updated match result, or {@code null} if validation
     *         fails
     */
    @Nullable
    MatchResultInfo checkConditions(@Nullable MatchResultInfo matchResultInfo,
            @NonNull LogicServices services);

    /**
     * Matches a template formula (typically from the "assumes" part of a taclet) against a
     * list of constraint formulas (e.g., from a sequent's antecedent or succedent),
     * using the given initial match conditions.
     *
     * @param toMatch a list of formulas to attempt matching with {@code template}
     * @param template the formula template to match against each formula in {@code toMatch}
     * @param matchCond the current {@link MatchResultInfo} representing the current match status
     * @param services the {@link LogicServices} providing contextual information
     * @return a result containing the successfully matched formulas and their associated match
     *         conditions
     */
    @NonNull
    AssumesMatchResult matchAssumes(@NonNull Iterable<@NonNull AssumesFormulaInstantiation> toMatch,
            @NonNull Term template, @NonNull MatchResultInfo matchCond,
            @NonNull LogicServices services);

    /**
     * Matches a list of formula instantiations against the full "assumes" sequent of a taclet,
     * starting with the given initial match conditions.
     * <p>
     * <strong>Precondition:</strong> {@code toMatch.size() == ifSequent().size()}
     *
     * @param toMatch a list of formulas to attempt matching with {@code template}
     * @param matchCond the current {@link MatchResultInfo} representing the current match status
     * @param services the {@link LogicServices} providing contextual information
     * @return the resulting match conditions if successful; {@code null} otherwise
     */
    @Nullable
    MatchResultInfo matchAssumes(@NonNull Iterable<AssumesFormulaInstantiation> toMatch,
            @NonNull MatchResultInfo matchCond, @NonNull LogicServices services);

    /**
     * Matches a schema variable to a syntax element under the given match conditions.
     *
     * @param sv the {@link SchemaVariable} to match
     * @param se the candidate {@link SyntaxElement}
     * @param matchCond the current {@link MatchResultInfo} representing the current match status
     * @param services the {@link LogicServices} providing contextual information
     * @return updated match result if successful; {@code null} if no match was possible
     */
    @Nullable
    MatchResultInfo matchSV(SchemaVariable sv, SyntaxElement se, MatchResultInfo matchCond,
            LogicServices services);
}
