package de.uka.ilkd.key.pp;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;

/**
 * This filter takes a {@link PosInOccurrence} and only shows the subterm at that position.
 * 
 * @author lanzinger
 */
public class ShowSelectedSequentPrintFilter extends SequentPrintFilter {
    
    private PosInOccurrence pos;

    public ShowSelectedSequentPrintFilter(PosInOccurrence pos) {
        this.pos = pos;
    }
    
    @Override
    protected void filterSequent() { }

    @Override
    public ImmutableList<SequentPrintFilterEntry> getFilteredAntec() {
        if (pos.isInAntec()) {
            return ImmutableSLList.<SequentPrintFilterEntry>nil().append(new Entry(pos));
        } else {
            return ImmutableSLList.<SequentPrintFilterEntry>nil();
        }
    }
    
    @Override
    public ImmutableList<SequentPrintFilterEntry> getFilteredSucc() {
        if (!pos.isInAntec()) {
            return ImmutableSLList.<SequentPrintFilterEntry>nil().append(new Entry(pos));
        } else {
            return ImmutableSLList.<SequentPrintFilterEntry>nil();
        }
    }
    
    public static class Entry implements SequentPrintFilterEntry {
        
        private SequentFormula filtered;
        private SequentFormula original;
        
        private Entry(PosInOccurrence pos) {
            filtered = new SequentFormula(pos.subTerm());
            original = pos.sequentFormula();
        }

        @Override
        public SequentFormula getFilteredFormula() {
            return filtered;
        }

        @Override
        public SequentFormula getOriginalFormula() {
            return original;
        }
        
    }
}
