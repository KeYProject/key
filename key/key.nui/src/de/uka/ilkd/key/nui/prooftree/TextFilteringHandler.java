package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedList;

/**
 * Performs the filtering.
 * 
 * @author Matthias Schultheis
 * @version 1.0
 *
 */
public final class TextFilteringHandler {

    /**
     * Utility class should not be instantiated.
     */
    private TextFilteringHandler() {
    }

    /**
     * Returns a subtree consisting of only matching nodes.
     * 
     * @param root
     *            the root node of the source tree
     * @param search
     *            the query used for filtering
     * @return the root node of a filtered tree or null if not found
     * @throws CloneNotSupportedException
     */
    public static NUINode getMatchedSubtree(final NUINode root, final String search)
            throws CloneNotSupportedException {
        // label matches -> copy subtree
        if (matchesFilter(root, search)) {
            // TODO set parent??
            final NUINode filteredTreeRoot = root.clone();

            return filteredTreeRoot;
        }
        // branch nodes -> look at children
        else if (root instanceof NUIBranchNode) {
            final LinkedList<NUINode> matchedChildren = new LinkedList<>();
            final NUIBranchNode rootBN = (NUIBranchNode) root;

            // add matching children
            for (final NUINode child : rootBN.getChildren()) {
                final NUINode childMatchedSubTree = getMatchedSubtree(child, search);
                if (childMatchedSubTree != null) {
                    matchedChildren.add(childMatchedSubTree);
                }
            }

            // if children match it is also a match
            if (!matchedChildren.isEmpty()) {

                final NUIBranchNode filteredRoot = rootBN.cloneWithoutChildren();
                filteredRoot.setChildren(matchedChildren);

                // set parent for children
                matchedChildren.forEach((child) -> child.setParent(filteredRoot));

                return filteredRoot;

            }
        }
        // root does not match and is no branch node
        // OR no children match -> branch does not match
        return null;
    }

    /**
     * Checks if a node matches a filter rule.
     * 
     * @param node
     *            the node to check
     * @param filter
     *            the filter string
     * @return true iff the node matches the filter rule
     */
    private static boolean matchesFilter(final NUINode node, final String filter) {
        final String lblLC = node.getLabel().toLowerCase();
        final String filterLC = filter.toLowerCase();
        return lblLC.contains(filterLC);
    }
}
