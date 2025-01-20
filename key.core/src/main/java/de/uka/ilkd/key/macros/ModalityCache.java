/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.Map;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Modality;

import org.key_project.util.LRUCache;

/**
 * Caches whether a Term contains a modality operation.
 *
 * @author Julian Wiesler
 */
public class ModalityCache {
    /** the cache */
    private final Map<Term, Boolean> termCache = new LRUCache<>(2000);

    /**
     * a single element cache for the sequent
     * -> Caching more than one sequent did not help since the autopilot rarely revisits nodes
     */
    private Sequent sequent = null;
    /**
     * the value of the sequent cache
     */
    private boolean sequentValue = false;

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

        if (term.containsLabel(ParameterlessTermLabel.SELF_COMPOSITION_LABEL)) {
            // ignore self composition terms
            hasModality = false;
        } else if (term.op() instanceof Modality) {
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
        if (this.sequent == sequent) {
            return sequentValue;
        }

        var result = false;
        for (SequentFormula sequentFormula : sequent) {
            if (termHasModality(sequentFormula.formula())) {
                result = true;
                break;
            }
        }

        this.sequent = sequent;
        sequentValue = result;
        return result;
    }
}
