package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A proof tree filter that can be used to hide all closed nodes.
 * 
 * @author Matthias Schultheis
 *
 */
@FilterAnnotation(isFilter = true)
public class FilterHideClosed implements ProofTreeFilter {

    @Override
    public boolean test(final NUINode node) {
        return !node.isClosed();
    }

    @Override
    public String getContextMenuItemText() {
        return "Hide Closed";
    }
}
