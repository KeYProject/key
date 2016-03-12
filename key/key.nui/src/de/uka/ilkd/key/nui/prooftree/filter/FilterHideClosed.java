package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A proof tree filter that can be used to hide all closed nodes.
 * @author Matthias Schultheis
 *
 */
public class FilterHideClosed implements ProofTreeFilter {
    
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean test(final NUINode node) {
        return !node.isClosed();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getContextMenuItemText() {
        return "Hide Closed";
    }
}
