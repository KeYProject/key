package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A proof tree filter that is used to show an non-filtered tree.
 * 
 * @author Matthias Schultheis
 *
 */
public class FilterShowAll implements ProofTreeFilter {

    @Override
    public String getContextMenuItemText() {
        return "";
    }

    @Override
    public boolean test(final NUINode node) {
        return true;
    }
}
