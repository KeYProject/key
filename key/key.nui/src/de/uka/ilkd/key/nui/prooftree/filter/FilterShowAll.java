package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A proof tree filter that is used to show an non-filtered tree.
 * 
 * @author Matthias Schultheis
 *
 */
@SuppressWarnings("PMD.AtLeastOneConstructor")
//PMD will also complain if adding the constructor, then saying "avoid useless constructors"
public class FilterShowAll implements ProofTreeFilter {

    @Override
    public String getContextMenuItemText() {
        return "";
    }

    @Override
    @SuppressWarnings("PMD.JUnit4TestShouldUseTestAnnotation")
    public boolean test(final NUINode node) {
        return true;
    }
}
