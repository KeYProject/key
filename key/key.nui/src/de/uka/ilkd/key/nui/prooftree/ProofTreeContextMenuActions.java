package de.uka.ilkd.key.nui.prooftree;

import de.uka.ilkd.key.nui.controller.NUIController;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.control.TreeItem;

/**
 * This class contains actions for the context menu
 * @author  Matthias Schultheis
 * @version 1.0
 */
public class ProofTreeContextMenuActions {
	
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
}
