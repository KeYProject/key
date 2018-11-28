package de.uka.ilkd.key.pp;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import com.sun.accessibility.internal.resources.accessibility;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;

/**
 * This filter takes a {@link PosInOccurrence} and only shows the sub-term at that position.
 * 
 * @author lanzinger
 */
public class ShowSelectedSequentPrintFilter extends SequentPrintFilter {
    
    private PosInOccurrence pos;

    /**
     * Create a new {@link ShowSelectedSequentPrintFilter}.
     * 
     * @param pos the position of the only sub-term to show.
     */
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
    
    /**
     * An Entry in {@link accessibility} {@link ShowSelectedSequentPrintFilter}.
     * 
     * The only entry created for such a filter contains the sub-term at the specified position as
     * filtered term ({@link #getFilteredFormula()}) and that sub-term's top-level term as
     * the original ({@link #getOriginalFormula()}).
     * 
     * @author lanzinger
     */
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
