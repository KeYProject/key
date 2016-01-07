package de.uka.ilkd.key.nui.prooftree;

import java.io.IOException;
import java.net.URL;

import de.uka.ilkd.key.nui.controller.NUIController;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import javafx.fxml.FXMLLoader;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.TreeItem;
import javafx.scene.layout.Pane;

/**
 * This class represents a context menu used for proof tree items
 * 
 * @author Matthias Schultheis
 * @author Stefan Pilot
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
     * 
     * @param node
     *            the tree node the context menu is for
     * @param treeItem
     *            the treeItem of node
     */
    public ProofTreeContextMenu(NUINode node, TreeItem<NUINode> treeItem) {
        this.node = node;
        this.treeItem = treeItem;

        addMenuItemExpandAll();
        addMenuItemCollapseAll();
        addMenuItemSearch();
    }

    /**
     * adds the entry ExpandAll to the context menu
     */
    private void addMenuItemExpandAll() {
        MenuItem miExpandAll = new MenuItem("Expand All"); // TODO
        getItems().add(miExpandAll);
        miExpandAll.setOnAction(t -> ProofTreeContextMenuActions.expandAll(treeItem));
    }

    /**
     * adds the entry ExpandAll to the context menu
     */
    private void addMenuItemCollapseAll() {
        MenuItem miCollapseAll = new MenuItem("Collapse All"); // TODO
        getItems().add(miCollapseAll);
        miCollapseAll.setOnAction(t -> ProofTreeContextMenuActions.collapseAll(treeItem));
    }

    /**
     * adds the entry Search... to the context menu
     */
    private void addMenuItemSearch() {
        MenuItem mISearch = new MenuItem("Search...");
        this.getItems().add(mISearch);
        mISearch.setOnAction(t -> {
            try {
                NUIController.getInstance().createComponent(".searchView", NUIController.Place.LEFT,
                        ".searchView.fxml");
            }
            catch (IllegalArgumentException e) {
                NUIController.getInstance().createComponent(".searchView", NUIController.Place.HIDDEN,
                        ".searchView.fxml");
            }
        });
    }

}
