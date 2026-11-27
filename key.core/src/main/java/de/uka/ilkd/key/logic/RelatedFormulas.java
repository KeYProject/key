/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import static de.uka.ilkd.key.logic.equality.TermLabelsProperty.TERM_LABELS_PROPERTY;

/**
 * Computes the formulae of a sequent that are transitively related to a given term by syntax.
 * <p>
 * A formula is related to a term iff it is reachable from that term in the bipartite graph whose
 * nodes are the formulae and all their subterms, and whose edges connect a formula with each of its
 * subterms. Hence all formulae are kept that share a syntactic subterm with the seed term, possibly
 * through a chain of such shared subterms.
 *
 * @author A. Weigl, W. Pfeifer
 */
public final class RelatedFormulas {

    private RelatedFormulas() {
    }

    /**
     * Computes the formulae of the given sequent that are transitively related to the seed term.
     * <p>
     * The formula that was clicked (the one containing the seed term) is always part of the result.
     *
     * @param sequent the sequent whose formulae are inspected
     * @param seed the term to which the returned formulae are related
     * @param clickedFormula the formula in which the seed term occurs, as clicked by the user
     * @return the set of related formulae of the sequent, or {@link Optional#empty()} if
     *         {@code clickedFormula} does not occur in {@code sequent}
     */
    public static Optional<Set<SequentFormula>> computeKeptFormulas(Sequent sequent, JTerm seed,
            SequentFormula clickedFormula) {
        Optional<SequentFormula> match = findMatchingFormula(sequent, clickedFormula);
        if (match.isEmpty()) {
            return Optional.empty();
        }

        Map<Term, Set<SequentFormula>> index = indexSubterms(sequent);
        Set<Term> visited = new HashSet<>();
        Deque<Term> queue = new ArrayDeque<>();

        Set<SequentFormula> kept = new LinkedHashSet<>();
        Set<SequentFormula> processed = new HashSet<>();
        // The clicked formula is always kept; use the instance that occurs in the sequent. Its
        // subterms seed the propagation.
        kept.add(match.get());
        if (processed.add(match.get())) {
            enqueueNewSubterms(match.get().formula(), visited, queue);
        }
        visited.add(seed);
        queue.add(seed);

        while (!queue.isEmpty()) {
            Term term = queue.poll();
            for (SequentFormula formula : index.getOrDefault(term, Set.of())) {
                kept.add(formula);
                if (processed.add(formula)) {
                    enqueueNewSubterms(formula.formula(), visited, queue);
                }
            }
        }
        return Optional.of(kept);
    }

    private static void enqueueNewSubterms(Term term, Set<Term> visited, Deque<Term> queue) {
        for (Term sub : allSubterms(term)) {
            if (visited.add(sub)) {
                queue.add(sub);
            }
        }
    }

    /**
     * @param sequent the sequent that is displayed
     * @param kept the formulae that would be kept
     * @return {@code true} iff hiding would not remove any formula of the sequent
     */
    public static boolean hidesNothing(Sequent sequent, Set<SequentFormula> kept) {
        return kept.size() >= sequent.size();
    }

    /**
     * Finds the formula of the given sequent that is syntactically equal to {@code clickedFormula},
     * ignoring term labels.
     *
     * @param sequent a sequent
     * @param clickedFormula a formula that the user clicked
     * @return the matching formula of the sequent or empty, if there is none
     */
    private static Optional<SequentFormula> findMatchingFormula(Sequent sequent,
            SequentFormula clickedFormula) {
        Term clickedTerm = clickedFormula.formula();
        for (SequentFormula sf : sequent.antecedent()) {
            if (TERM_LABELS_PROPERTY.equalsModThisProperty(sf.formula(), clickedTerm)) {
                return Optional.of(sf);
            }
        }
        for (SequentFormula sf : sequent.succedent()) {
            if (TERM_LABELS_PROPERTY.equalsModThisProperty(sf.formula(), clickedTerm)) {
                return Optional.of(sf);
            }
        }
        return Optional.empty();
    }

    /**
     * Builds the index that maps every subterm occurring in the sequent to the formulae containing
     * it.
     */
    private static Map<Term, Set<SequentFormula>> indexSubterms(Sequent sequent) {
        Map<Term, Set<SequentFormula>> index = new HashMap<>();
        for (SequentFormula sf : sequent.antecedent()) {
            indexFormula(sf, index);
        }
        for (SequentFormula sf : sequent.succedent()) {
            indexFormula(sf, index);
        }
        return index;
    }

    private static void indexFormula(SequentFormula sf, Map<Term, Set<SequentFormula>> index) {
        for (Term subterm : allSubterms(sf.formula())) {
            index.computeIfAbsent(subterm, k -> new LinkedHashSet<>()).add(sf);
        }
    }

    /**
     * Returns all subterms of the given term, the term itself included. Java blocks of modalities
     * are not traversed.
     */
    private static Set<Term> allSubterms(Term term) {
        Set<Term> result = new LinkedHashSet<>();
        collectSubterms(term, result);
        return result;
    }

    private static void collectSubterms(Term term, Set<Term> result) {
        for (Term sub : term.subs()) {
            collectSubterms(sub, result);
        }
        result.add(term);
    }
}
