package de.uka.ilkd.key.nui.prooftree;

import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.TreeItem;

/**
 * This class represents a context menu used for proof tree items
 * @author  Matthias Schultheis
 * @version 1.0
 */
public class ProofTreeContextMenu extends ContextMenu {
	
	/**
	 * the tree node the context menu is for
	 */
	NUINode node;
	
	/**
	 * the treeItem of node
	 */
	TreeItem<NUINode> treeItem;
	
	/**
	 * puts in the contextmenu
	 * @param node the tree node the context menu is for
	 * @param treeItem the treeItem of node
	 */
	public ProofTreeContextMenu(NUINode node, TreeItem<NUINode> treeItem) {
		this.node = node;
		this.treeItem = treeItem;
		
		addMenuItemExpandAll();
		addMenuItemCollapseAll();
	}
	
	/**
	 * adds the entry ExpandAll to the context menu
	 */
	private void addMenuItemExpandAll() {
		MenuItem miExpandAll = new MenuItem("Expand All"); //TODO
		getItems().add(miExpandAll);
		miExpandAll.setOnAction(t -> ProofTreeContextMenuActions.expandAll(treeItem));
	}
	
	/**
	 * adds the entry ExpandAll to the context menu
	 */
	private void addMenuItemCollapseAll() {
		MenuItem miCollapseAll = new MenuItem("Collapse All"); //TODO
		getItems().add(miCollapseAll);
		miCollapseAll.setOnAction(t -> ProofTreeContextMenuActions.collapseAll(treeItem));
	}
}
