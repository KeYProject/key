package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUIBranchNode;
import de.uka.ilkd.key.nui.prooftree.NUILeafNode;
import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A proof tree filter that can be used to hide all intermediate proof steps
 * between branch nodes and leaf nodes.
 * 
 * @author Matthias Schultheis
 *
 */
@FilterAnnotation(isFilter = true)
public class FilterHideIntermediate implements ProofTreeFilter {

    @Override
    public boolean test(final NUINode node) {
        return node instanceof NUIBranchNode || node instanceof NUILeafNode;
    }

    @Override
    public String getContextMenuItemText() {
        return "Hide Intermediate";
    }
}
