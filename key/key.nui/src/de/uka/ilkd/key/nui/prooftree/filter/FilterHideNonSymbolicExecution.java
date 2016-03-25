package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUIBranchNode;
import de.uka.ilkd.key.nui.prooftree.NUILeafNode;
import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A proof tree filter that can be used to hide nodes that are no symbolic
 * executions.
 * 
 * @author Matthias Schultheis
 *
 */
@SuppressWarnings("PMD.AtLeastOneConstructor")
//PMD will also complain if adding the constructor, then saying "avoid useless constructors"
@FilterAnnotation(isFilter = true)
public class FilterHideNonSymbolicExecution implements ProofTreeFilter {

    @Override
    public String getContextMenuItemText() {
        return "Hide Non-Symbolic-Execution";
    }

    @Override
    @SuppressWarnings("PMD.JUnit4TestShouldUseTestAnnotation")
    public boolean test(final NUINode node) {
        if (node instanceof NUIBranchNode || node instanceof NUILeafNode) {
            return true;
        }
        return node.isSymbolicExecution();
    }
}
