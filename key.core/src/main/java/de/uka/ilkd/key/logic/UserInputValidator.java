/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.List;
import java.util.Optional;

import de.uka.ilkd.key.logic.sort.GenericSort;

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
 * To add a new user-input check (e.g. a stricter well-typedness check), add a {@link Check} to
 * {@link #CHECKS}; no boundary needs to change. To add a new boundary, call
 * {@link #validate(JTerm, String)} / {@link #validate(Sequent, String)} there and raise the
 * boundary's natural (positioned) exception with the returned message.
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
         * @return an error message if {@code term} is invalid for user input, otherwise empty
         */
        Optional<String> validate(JTerm term, String context);
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
     * @return the first validation error, or empty if {@code term} is acceptable
     */
    public static Optional<String> validate(@Nullable JTerm term, String context) {
        if (term == null) {
            return Optional.empty();
        }
        for (Check check : CHECKS) {
            Optional<String> issue = check.validate(term, context);
            if (issue.isPresent()) {
                return issue;
            }
        }
        return Optional.empty();
    }

    /**
     * Runs all registered checks on every formula of {@code sequent}.
     *
     * @param sequent a sequent produced from user input, may be {@code null}
     * @param context a short description of the origin for the error message
     * @return the first validation error, or empty if the sequent is acceptable
     */
    public static Optional<String> validate(@Nullable Sequent sequent, String context) {
        if (sequent == null) {
            return Optional.empty();
        }
        for (SequentFormula sf : sequent) {
            Optional<String> issue = validate((JTerm) sf.formula(), context);
            if (issue.isPresent()) {
                return issue;
            }
        }
        return Optional.empty();
    }

    /** Check: generic sorts (schematic taclet placeholders) must not occur in a concrete term. */
    private static Optional<String> checkNoGenericSort(JTerm term, String context) {
        GenericSort generic = GenericSortDetector.findIn(term);
        if (generic == null) {
            return Optional.empty();
        }
        return Optional.of("The generic sort '" + generic.name() + "' must not occur in " + context
            + ". Generic sorts may only be used in taclets.");
    }
}
