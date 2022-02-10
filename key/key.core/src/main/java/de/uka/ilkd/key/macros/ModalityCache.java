package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import org.key_project.util.LRUCache;

import java.util.Map;

public class ModalityCache {
    private final Map<Term, Boolean> termCache = new LRUCache<>(2000);

    // Caching more than one sequent does not help since autopilot rarely revisits nodes
    private Sequent sequent = null;
    private boolean sequentValue = false;

    public ModalityCache() {}

    /*
     * find a modality term
     */
    private boolean termHasModality(Term term) {
        Boolean cached = termCache.get(term);
        if (cached != null) {
            return cached;
        }

        // This is the faster comparison but rarely returns
        if (term.op() instanceof Modality) {
            return true;
        }

        var hasModality = false;
        for (Term sub : term.subs()) {
            if (termHasModality(sub)) {
                hasModality = true;
                break;
            }
        }

        termCache.put(term, hasModality);
        return hasModality;
    }

    /*
     * find a modality term in a sequent
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
