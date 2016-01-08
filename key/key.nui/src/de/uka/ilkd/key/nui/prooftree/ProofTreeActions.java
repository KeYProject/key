package de.uka.ilkd.key.nui.prooftree;

import javafx.scene.control.TreeItem;

/**
 * This utility class contains actions for the context menu.
 * @author  Matthias Schultheis
 * @version 1.0
 */
public final class ProofTreeActions {
	
	/**
	 * The private constructor is not called as
	 * it is only a utility class.
	 */
	private ProofTreeActions() {
	}
	
	/**
	 * expands an item and all of its children
	 * @param treeItem the item for applying the action to
	 */
	public static void expandAll(TreeItem<NUINode> treeItem) {
		treeItem.setExpanded(true);
		for(TreeItem<NUINode> child : treeItem.getChildren()) {
			expandAll(child);
		}
	}
	
	/**
	 * collapses an item and all of its children
	 * @param treeItem the item for applying the action to
	 */
	public static void collapseAll(TreeItem<NUINode> treeItem) {
		treeItem.setExpanded(false);
		for(TreeItem<NUINode> child : treeItem.getChildren()) {
			collapseAll(child);
		}
	}
	
	/**
	 * Repaints a tree item in its treeView.
	 * This is a workaround as JavaFX doesn't support this function.
	 * It works by triggering the internal treeCell update method
	 * such that the treeCell is rendered again.
	 * @param treeItem the treeItem to refresh
	 */
	public static void refeshTreeItem(final TreeItem<NUINode> treeItem) {
		int index = treeItem.getParent().getChildren().indexOf(treeItem);
		treeItem.getParent().getChildren().set(index, treeItem);
	}
}
