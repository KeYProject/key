/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.ArrayList;
import java.util.List;

import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.Nullable;

/**
 * Central place for validations that must be applied to <em>terms/sequents produced from user
 * input</em> (problem sections, JML expressions, interactive taclet instantiations, ...), but not
 * to terms created internally during automatic proof search.
 * <p>
 * The point of this class is twofold:
 * <ul>
 * <li>checks are <b>defined once</b> here ({@link #CHECKS}) instead of being inlined at every
 * parser boundary, and</li>
 * <li>because the validator is only invoked at user-input boundaries, every registered check is
 * automatically scoped to user input only — automatic term creation never runs them, so there is
 * no extra cost on the proof-search hot path.</li>
 * </ul>
 * Each check returns <em>all</em> problems it finds (not just the first), so a boundary can report
 * them together. The callers turn the returned messages into the boundary's natural exception; the
 * problem/JML boundaries bundle them into a {@code BuildingExceptions} so that the shared
 * {@code ExceptionTools#getMessages} extraction (used by both the GUI {@code IssueDialog} and the
 * console) reports every problem with its own entry.
 * <p>
 * To add a new user-input check (e.g. a stricter well-typedness check), add a {@link Check} to
 * {@link #CHECKS}; no boundary needs to change. To add a new boundary, call
 * {@link #validate(JTerm, String)} / {@link #validate(Sequent, String)} there and raise the
 * boundary's exception with the returned messages.
 *
 * @author KeY developers
 */
public final class UserInputValidator {

    /**
     * A single validation applied to a user-supplied term.
     */
    @FunctionalInterface
    public interface Check {
        /**
         * @param term a term produced from user input
         * @param context a short human-readable description of where the term came from, used in
         *        the error message (e.g. {@code "a \\problem"})
         * @return one error message per problem found in {@code term} (empty if it is acceptable)
         */
        List<String> validate(JTerm term, String context);
    }

    /** The registered user-input checks. Add new checks here. */
    private static final List<Check> CHECKS = List.of(
        UserInputValidator::checkNoGenericSort);

    private UserInputValidator() {}

    /**
     * Runs all registered checks on {@code term}.
     *
     * @param term a term produced from user input, may be {@code null}
     * @param context a short description of the origin for the error message (e.g. {@code "a
     *        \\problem"}, {@code "a JML expression"}, {@code "an instantiation"})
     * @return all validation errors (empty if {@code term} is acceptable)
     */
    public static List<String> validate(@Nullable JTerm term, String context) {
        if (term == null) {
            return List.of();
        }
        List<String> issues = new ArrayList<>();
        for (Check check : CHECKS) {
            issues.addAll(check.validate(term, context));
        }
        return issues;
    }

    /**
     * Runs all registered checks on every formula of {@code sequent}.
     *
     * @param sequent a sequent produced from user input, may be {@code null}
     * @param context a short description of the origin for the error message
     * @return all validation errors (empty if the sequent is acceptable)
     */
    public static List<String> validate(@Nullable Sequent sequent, String context) {
        if (sequent == null) {
            return List.of();
        }
        List<String> issues = new ArrayList<>();
        for (SequentFormula sf : sequent) {
            issues.addAll(validate((JTerm) sf.formula(), context));
        }
        return issues;
    }

    /** Check: generic sorts (schematic taclet placeholders) must not occur in a concrete term. */
    private static List<String> checkNoGenericSort(JTerm term, String context) {
        List<String> issues = new ArrayList<>();
        for (Sort sort : GenericSortDetector.findIn(term)) {
            issues.add("The sort '" + sort.name() + "' must not occur in " + context
                + "; it is or contains a generic sort, which may only appear in taclets.");
        }
        return issues;
    }
}
