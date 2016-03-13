package de.uka.ilkd.key.nui.prooftree;

import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;

/**
 * This class represents a context menu used for proof tree items.
 * 
 * @author Matthias Schultheis
 * @author Stefan Pilot
 * @version 1.0
 */
public class ProofTreeContextMenu extends ContextMenu {

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

    private final FilteringHandler fh;

    private TreeViewController treeViewController = null;

    /**
     * The label of the context menu "expand all" label.
     */
    private static final String LBL_EXPAND_ALL = "Expand All";

    /**
     * The label of the context menu "expand below" label.
     */
    private static final String LBL_EXPAND_BELOW = "Expand Below";

    /**
     * The label of the context menu "collapse all" label.
     */
    private static final String LBL_COLLAPSE_ALL = "Collapse All";

    /**
     * The label of the context menu "collapse below" label.
     */
    private static final String LBL_COLLAPSE_BELOW = "Collapse Below";

    /**
     * The label of the context menu "search" label.
     */
    private static final String LBL_SEARCH = "Search";

    /**
     * The constructor.
     * 
     * @param treeItem
     *            the treeItem of node
     * @param treeView
     *            the treeview that treeItem is in
     * @param icf
     *            an icon factory for creating icons
     */
    public ProofTreeContextMenu(final TreeItem<NUINode> treeItem,
            final TreeView<NUINode> treeView, final IconFactory icf,
            final FilteringHandler fh, TreeViewController tvc) {
        super();

        this.treeItem = treeItem;
        this.treeView = treeView;

        this.icf = icf;
        this.fh = fh;
        this.treeViewController = tvc;

        // Add dummy so that the context menu can be displayed.
        // It is put in in the method "show".
        addSeparator();
    }

    /**
     * {@inheritDoc} This method is called to show the contextmenu. Displays and
     * fills the context menu.
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
        addMenuItemsFilter();
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
        final MenuItem miExpandAll = new MenuItem(LBL_EXPAND_ALL);
        miExpandAll.setGraphic(icf.getImage(IconFactory.EXPAND));
        getItems().add(miExpandAll);
        miExpandAll.setOnAction(
                aEvt -> ProofTreeActions.expandAll(treeView.getRoot()));
    }

    /**
     * Adds the entry ExpandAll to the context menu.
     */
    private void addMenuItemExpandBelow() {
        final MenuItem miExpand = new MenuItem(LBL_EXPAND_BELOW);
        getItems().add(miExpand);
        miExpand.setOnAction(aEvt -> ProofTreeActions.expandBelow(treeItem));
    }

    /**
     * Adds the entry ExpandAll to the context menu.
     */
    private void addMenuItemCollapseAll() {
        final MenuItem miCollapseAll = new MenuItem(LBL_COLLAPSE_ALL);
        miCollapseAll.setGraphic(icf.getImage(IconFactory.COLLAPSE));
        getItems().add(miCollapseAll);
        miCollapseAll.setOnAction(
                aEvt -> ProofTreeActions.collapseAll(treeView.getRoot()));
    }

    /**
     * Adds the entry ExpandAll to the context menu.
     */
    private void addMenuItemCollapseBelow() {
        final MenuItem miCollapse = new MenuItem(LBL_COLLAPSE_BELOW);
        getItems().add(miCollapse);
        miCollapse
                .setOnAction(aEvt -> ProofTreeActions.collapseBelow(treeItem));
    }

    /**
     * Adds the entry Search to the context menu.
     */
    private void addMenuItemSearch() {
        final MenuItem mISearch = new MenuItem(LBL_SEARCH);
        getItems().add(mISearch);
        mISearch.setGraphic(icf.getImage(IconFactory.SEARCH));
        mISearch.setAccelerator(KeyCombination.keyCombination("Ctrl+F"));
        mISearch.setOnAction(aEvt -> treeViewController.openSearchView());
        
    }

    private void addMenuItemsFilter() {
        Map<ProofTreeFilter, Boolean> a = fh.getFiltersMap();
        for (Entry<ProofTreeFilter, Boolean> k : a.entrySet()) {
            addMenuItemFilter(k.getKey(), k.getValue());
        }
    }

    private void addMenuItemFilter(ProofTreeFilter k, boolean initState) {
        CheckMenuItem cmi = new CheckMenuItem(k.getContextMenuItemText());
        cmi.setSelected(initState);

        cmi.selectedProperty().addListener(new ChangeListener<Boolean>() {
            @Override
            public void changed(ObservableValue<? extends Boolean> observable,
                    Boolean oldValue, Boolean newValue) {
                if (fh.getFilterStatus(k) != newValue) {
                    fh.toggleFilteringStatus(k);
                }
            }

        });

        getItems().add(cmi);
    }

}
