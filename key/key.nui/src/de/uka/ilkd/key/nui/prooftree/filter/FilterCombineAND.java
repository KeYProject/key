package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A filter that can be used to combine two
 * filters via AND.
 * @author Matthias Schultheis
 *
 */
public class FilterCombineAND implements ProofTreeFilter {
    
    /**
     * The first filter used for combination.
     */
    ProofTreeFilter f1;
    
    /**
     * The second filter used for combination.
     */
    ProofTreeFilter f2;
    
    /**
     * Constructor.
     * @param f1 The first filter.
     * @param f2 The second filter.
     */
    public FilterCombineAND(ProofTreeFilter f1, ProofTreeFilter f2) {
        this.f1 = f1;
        this.f2 = f2;
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean test(final NUINode node) {
        return f1.test(node) && f2.test(node);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getContextMenuItemText() {
        return "";
    }
}
