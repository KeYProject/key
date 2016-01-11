package de.uka.ilkd.key.nui.prooftree;

import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.controller.NUIController;
import de.uka.ilkd.key.nui.controller.NUIController.Place;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

/**
 * This class represents a context menu used for proof tree items.
 * 
 * @author Matthias Schultheis
 * @author Stefan Pilot
 * @version 1.0
 */
public class ProofTreeContextMenu extends ContextMenu {

    /**
     * The tree node the context menu is for.
     */
    @SuppressWarnings("unused")
	private final NUINode node;

    /**
     * The treeItem of node.
     */
    private final TreeItem<NUINode> treeItem;
    
    /**
     * The treeView that node is in.
     */
    private final TreeView<NUINode> treeView;
    
    /**
     * The IconFactory used to create the required icons.
     */
    private final IconFactory icf;

    /**
     * The constructor.
     * @param treeItem
     *            the treeItem of node
     * @param treeView
     *            the treeview that treeItem is in
     * @param icf
     * 	          an icon factory for creating icons
     */
    public ProofTreeContextMenu(final TreeItem<NUINode> treeItem, 
    		final TreeView<NUINode> treeView, final IconFactory icf) {
    	super();
    	
    	this.treeItem = treeItem;
        this.node = treeItem.getValue();
        this.treeView = treeView;
        
        this.icf = icf;
        
        // Add dummy so that the context menu can be displayed.
        // It is put in in the method "show".
        addSeparator();
    }
    
    /**
     * {@inheritDoc}
     * This method is called to show the contextmenu.
     * Displays and fills the context menu.
     */
	@Override
    public final void show() {
    	super.show();
    	
    	// clear current entries
    	getItems().clear();
    	
    	// add appropriate entries
        addMenuItemExpandAll();
        addMenuItemExpandBelow();
        addMenuItemCollapseAll();
        addMenuItemCollapseBelow();
        
        addSeparator();
        
        addMenuItemSearch();
    }
    
    /**
     * Adds a separator to the context menu.
     */
    private void addSeparator() {
        getItems().add(new SeparatorMenuItem());
    }

    /**
     * Adds the entry ExpandAll to the context menu.
     */
    private void addMenuItemExpandAll() {
        final MenuItem miExpandAll = new MenuItem("Expand All"); //TODO
        miExpandAll.setGraphic(icf.getImage(IconFactory.EXPAND));
        getItems().add(miExpandAll);
        miExpandAll.setOnAction(t -> ProofTreeActions.expandAll(treeView.getRoot()));
    }
    
    /**
     * Adds the entry ExpandAll to the context menu.
     */
    private void addMenuItemExpandBelow() {
        final MenuItem miExpand = new MenuItem("Expand Below"); //TODO
        getItems().add(miExpand);
        miExpand.setOnAction(t -> ProofTreeActions.expandBelow(treeItem));
    }
    
    /**
     * Adds the entry ExpandAll to the context menu.
     */
    private void addMenuItemCollapseAll() {
        final MenuItem miCollapseAll = new MenuItem("Collapse All"); // TODO
        miCollapseAll.setGraphic(icf.getImage(IconFactory.COLLAPSE));
        getItems().add(miCollapseAll);
        miCollapseAll.setOnAction(t -> ProofTreeActions.collapseAll(treeView.getRoot()));
    }

    /**
     * Adds the entry ExpandAll to the context menu.
     */
    private void addMenuItemCollapseBelow() {
        final MenuItem miCollapse = new MenuItem("Collapse Below"); // TODO
        getItems().add(miCollapse);
        miCollapse.setOnAction(t -> ProofTreeActions.collapseBelow(treeItem));
    }

    /**
     * Adds the entry Search... to the context menu.
     */
    private void addMenuItemSearch() {
    	final MenuItem mISearch = new MenuItem("Search...");
    	this.getItems().add(mISearch);
    	mISearch.setGraphic(icf.getImage(IconFactory.SEARCH));
    	mISearch.setOnAction(t -> {
    	    Place p = NUIController.getInstance().getPlaceComponent().get("treeView");
    		try {
    			NUIController.getInstance().createOrMoveOrHideComponent(".searchView", p,
    					".searchView.fxml");
    		} catch (IllegalArgumentException e) {
    			NUIController.getInstance().createOrMoveOrHideComponent(".searchView", 
    					NUIController.Place.HIDDEN,	".searchView.fxml");
    		}
    	});
    }

}
