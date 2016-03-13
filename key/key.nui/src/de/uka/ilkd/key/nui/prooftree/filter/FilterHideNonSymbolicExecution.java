package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUIBranchNode;
import de.uka.ilkd.key.nui.prooftree.NUILeafNode;
import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A proof tree filter that can be used to hide nodes that
 * are no symbolic executions.
 * @author Matthias Schultheis
 *
 */
@FilterAnnotation(isFilter=true)
public class FilterHideNonSymbolicExecution implements ProofTreeFilter {
    
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean test(final NUINode node) {
        if (node instanceof NUIBranchNode) {
            return true;
        }
        else {
            return node.isSymbolicExecution();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getContextMenuItemText() {
        return "Hide Non-Symbolic-Execution";
    }
}
