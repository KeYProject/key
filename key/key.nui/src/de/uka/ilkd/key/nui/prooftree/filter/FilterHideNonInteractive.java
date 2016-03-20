package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUIBranchNode;
import de.uka.ilkd.key.nui.prooftree.NUILeafNode;
import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A proof tree filter that can be used to hide all nodes that are
 * non-interactive.
 * 
 * @author Matthias Schultheis
 */
@FilterAnnotation(isFilter = true)
public class FilterHideNonInteractive implements ProofTreeFilter {

    @Override
    public boolean test(final NUINode node) {
        if (node instanceof NUIBranchNode || node instanceof NUILeafNode) {
            return true;
        }
        return node.isInteractive();
    }

    @Override
    public String getContextMenuItemText() {
        return "Hide Non-Interactive";
    }

}