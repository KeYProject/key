package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUIBranchNode;
import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A proof tree filter that can be used to hide all nodes
 * that are non-interactive.
 * @author Matthias Schultheis
 */
@FilterAnnotation(isFilter=true)
public class FilterHideNonInteractive implements ProofTreeFilter {

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean test(final NUINode node) {
        if (node instanceof NUIBranchNode) {
            return true;
        }
        else {
            return node.isInteractive();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getContextMenuItemText() {
        return "Hide Non-Interactive";
    }

}