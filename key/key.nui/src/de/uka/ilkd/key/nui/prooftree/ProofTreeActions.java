package de.uka.ilkd.key.nui.prooftree;

import javafx.scene.control.TreeItem;

/**
 * This utility class contains actions for the context menu.
 * 
 * @author Matthias Schultheis
 * @version 1.0
 */
public final class ProofTreeActions {

    /**
     * The private constructor is not called as it is only a utility class.
     */
    private ProofTreeActions() {
    }

    /**
     * Expands an item and all of its children.
     * 
     * @param rootTreeItem
     *            the item for applying the action to
     */
    public static void expandAll(final TreeItem<NUINode> rootTreeItem) {
        rootTreeItem.setExpanded(true);
        rootTreeItem.getChildren().forEach((child) -> expandAll(child));
    }

    /**
     * Expands an item and all of its children.
     * 
     * @param treeItem
     *            the item for applying the action to
     */
    public static void expandBelow(final TreeItem<NUINode> treeItem) {
        treeItem.setExpanded(true);
        treeItem.getChildren().forEach((child) -> expandAll(child));

        // only expand siblings in case of no branch node
        if (!(treeItem.getValue() instanceof NUIBranchNode)) {
            final TreeItem<NUINode> nextSibling = treeItem.nextSibling();
            if (nextSibling != null) {
                expandBelow(nextSibling);
            }
        }
    }

    /**
     * Collapses an item and all of its children.
     * 
     * @param rootTreeItem
     *            the item for applying the action to
     */
    public static void collapseAll(final TreeItem<NUINode> rootTreeItem) {
        rootTreeItem.setExpanded(false);
        rootTreeItem.getChildren().forEach((child) -> collapseAll(child));
    }

    /**
     * Collapses an item and all of its children.
     * 
     * @param treeItem
     *            the item for applying the action to
     */
    public static void collapseBelow(final TreeItem<NUINode> treeItem) {
        treeItem.setExpanded(false);
        treeItem.getChildren().forEach((child) -> collapseAll(child));

        // only expand siblings in case of no branch node
        if (!(treeItem.getValue() instanceof NUIBranchNode)) {
            final TreeItem<NUINode> nextSibling = treeItem.nextSibling();
            if (nextSibling != null) {
                collapseBelow(nextSibling);
            }
        }
    }

    /**
     * Repaints a tree item in its treeView. This is a workaround as JavaFX
     * doesn't support this function. It works by triggering the internal
     * treeCell update method such that the treeCell is rendered again.
     * 
     * @param treeItem
     *            the treeItem to refresh
     */
    public static void refreshTreeItem(final TreeItem<NUINode> treeItem) {
        final int index = treeItem.getParent().getChildren().indexOf(treeItem);
        treeItem.getParent().getChildren().set(index, treeItem);
    }
}
