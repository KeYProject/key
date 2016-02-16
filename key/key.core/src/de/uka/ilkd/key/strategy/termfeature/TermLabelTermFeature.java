package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;

/** Termfeature which checks if a term has a specific label or any label at all */
public class TermLabelTermFeature extends BinaryTermFeature {
    
    public static final TermFeature HAS_ANY_LABEL = new TermLabelTermFeature(null);
    
    public static TermFeature create(TermLabel label) {
        return new TermLabelTermFeature(label);
    }


    private final TermLabel label;
    
    private TermLabelTermFeature(TermLabel label) {
        this.label = label;
    }

    @Override
    protected boolean filter(Term term, Services services) {
        if (label == null) {
            return term.hasLabels();
        }
        return term.containsLabel(label);
    }
}