package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A proof tree filter that can be used to hide all closed nodes.
 * 
 * @author Matthias Schultheis
 *
 */
@SuppressWarnings("PMD.AtLeastOneConstructor")
//PMD will also complain if adding the constructor, then saying "avoid useless constructors"
@FilterAnnotation(isFilter = true)
public class FilterHideClosed implements ProofTreeFilter {

    @Override
    public String getContextMenuItemText() {
        return "Hide Closed";
    }

    @Override
    @SuppressWarnings("PMD.JUnit4TestShouldUseTestAnnotation")
    public boolean test(final NUINode node) {
        return !node.isClosed();
    }
}
