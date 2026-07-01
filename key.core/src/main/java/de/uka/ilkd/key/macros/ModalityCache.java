/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.Map;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.JModality;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.ConcurrentLruCache;

/**
 * Caches whether a Term contains a modality operation.
 *
 * @author Julian Wiesler
 */
public class ModalityCache {
    /**
     * the cache. Thread-safe: a ModalityCache is shared across the parallel prover's workers via
     * the macro's filter strategy (see the class note on {@link #lastSequent}).
     */
    private final Map<Term, Boolean> termCache = new ConcurrentLruCache<>(2000);

    private record SequentResult(Sequent sequent, boolean value) {
    }

    /**
     * A single-element cache for the last sequent's result, kept <em>per thread</em>. A
     * {@link ModalityCache} is shared across the parallel prover's workers via the macro's filter
     * strategy -- {@link #hasModality} is reached from {@code Strategy#isApprovedApp}, which runs
     * off
     * the commit lock -- so a shared single field pair would race, and a torn read could return
     * another sequent's value. Caching more than one sequent did not help: the autopilot rarely
     * revisits nodes.
     */
    private final ThreadLocal<SequentResult> lastSequent = new ThreadLocal<>();

    /**
     * Constructor
     */
    public ModalityCache() {}

    /*
     * find a modality term
     */
    private boolean termHasModality(Term term) {
        Boolean cached = termCache.get(term);
        if (cached != null) {
            return cached;
        }

        boolean hasModality;

        if (((JTerm) term)
                .containsLabel(ParameterlessTermLabel.SELF_COMPOSITION_LABEL)) {
            // ignore self composition terms
            hasModality = false;
        } else if (term.op() instanceof JModality) {
            hasModality = true;
        } else {
            hasModality = false;
            for (Term sub : term.subs()) {
                if (termHasModality(sub)) {
                    hasModality = true;
                    break;
                }
            }
        }

        termCache.put(term, hasModality);
        return hasModality;
    }

    /**
     * Checks for a modality term in a sequent
     *
     * @param sequent the sequent
     * @return whether the sequent contained a modality term
     */
    public boolean hasModality(Sequent sequent) {
        final SequentResult last = lastSequent.get();
        if (last != null && last.sequent() == sequent) {
            return last.value();
        }

        var result = false;
        for (SequentFormula sequentFormula : sequent) {
            if (termHasModality(sequentFormula.formula())) {
                result = true;
                break;
            }
        }

        lastSequent.set(new SequentResult(sequent, result));
        return result;
    }
}
