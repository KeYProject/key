package de.uka.ilkd.key.nui.prooftree;

import java.util.Map;
import java.util.Map.Entry;
import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
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
     * The label of the context menu "collapse all" label.
     */
    private static final String LBL_COLLAPSE_ALL = "Collapse All";

    /**
     * The label of the context menu "collapse below" label.
     */
    private static final String LBL_COLLAPSE_BELOW = "Collapse Below";

    /**
     * The label of the context menu "expand all" label.
     */
    private static final String LBL_EXPAND_ALL = "Expand All";

    /**
     * The label of the context menu "expand below" label.
     */
    private static final String LBL_EXPAND_BELOW = "Expand Below";

    /**
     * The label of the context menu "search" label.
     */
    private static final String LBL_SEARCH = "Search";

    /**
     * The label of the contect menu "filter" label.
     */
    private static final String LBL_FILTER = "Filter by text";

    /**
     * The FilteringHandler used to filter the tree cells.
     */
    private final FilteringHandler filteringHandler;
    /**
     * The IconFactory used to create the required icons.
     */
    private final IconFactory icf;
    /**
     * The treeItem of node.
     */
    private final TreeItem<NUINode> treeItem;
    /**
     * The treeView that node is in.
     */
    private final TreeView<NUINode> treeView;
    /**
     * The reference to the TreeViewController associated with the TreeView.
     */
    private TreeViewController treeViewController;

    /**
     * The constructor.
     * 
     * @param treeItem
     *            the {@link TreeItem} of the node
     * @param treeView
     *            the {@link TreeView} which contains the treeItem
     * @param icf
     *            the {@link IconFactory} for creating icons
     * @param filteringHandler
     *            the {@link FilteringHandler} for filtering the tree
     * @param tvc
     *            the {@link TreeViewController} associated with the treeView
     */
    public ProofTreeContextMenu(final TreeItem<NUINode> treeItem, final TreeView<NUINode> treeView,
            final IconFactory icf, final FilteringHandler filteringHandler, final TreeViewController tvc) {
        super();

        this.treeItem = treeItem;
        this.treeView = treeView;

        this.icf = icf;
        this.filteringHandler = filteringHandler;
        this.treeViewController = tvc;

        // Add dummy so that the context menu can be displayed.
        // It is put in in the method "show".
        addSeparator();
    }

    /**
     * Getter.
     * 
     * @return the {@link FilteringHandler}.
     */
    public FilteringHandler getFh() {
        return filteringHandler;
    }

    /**
     * Getter.
     * 
     * @return the {@link IconFactory}.
     */
    public IconFactory getIcf() {
        return icf;
    }

    /**
     * Getter.
     * 
     * @return {@link TreeItem}&lt;{@link NUINode}&gt;
     */
    public TreeItem<NUINode> getTreeItem() {
        return treeItem;
    }

    /**
     * Getter.
     * 
     * @return the {@link TreeView}&lt;{@link NUINode}&gt;
     */
    public TreeView<NUINode> getTreeView() {
        return treeView;
    }

    /**
     * Getter.
     * 
     * @return the {@link TreeViewController}
     */
    public TreeViewController getTreeViewController() {
        return treeViewController;
    }

    /**
     * Setter.
     * 
     * @param treeVC
     *            the {@link TreeViewController} you want to set.
     */
    public void setTreeViewController(final TreeViewController treeVC) {
        this.treeViewController = treeVC;
    }

    /**
     * {@inheritDoc} This method is called to show the context menu. Displays
     * and fills the context menu.
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

        addSeparator();

        addMenuItemTextFilter();
    }

    /**
     * Adds the entry ExpandAll to the context menu.
     */
    private void addMenuItemCollapseAll() {
        final MenuItem miCollapseAll = new MenuItem(LBL_COLLAPSE_ALL);
        miCollapseAll.setGraphic(icf.getImage(IconFactory.COLLAPSE));
        getItems().add(miCollapseAll);
        miCollapseAll.setOnAction(aEvt -> ProofTreeActions.collapseAll(treeView.getRoot()));
    }

    /**
     * Adds the entry ExpandAll to the context menu.
     */
    private void addMenuItemCollapseBelow() {
        final MenuItem miCollapse = new MenuItem(LBL_COLLAPSE_BELOW);
        getItems().add(miCollapse);
        miCollapse.setOnAction(aEvt -> ProofTreeActions.collapseBelow(treeItem));
    }

    /**
     * Adds the entry ExpandAll to the context menu.
     */
    private void addMenuItemExpandAll() {
        final MenuItem miExpandAll = new MenuItem(LBL_EXPAND_ALL);
        miExpandAll.setGraphic(icf.getImage(IconFactory.EXPAND));
        getItems().add(miExpandAll);
        miExpandAll.setOnAction(aEvt -> ProofTreeActions.expandAll(treeView.getRoot()));
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
     * Configures the filter context menu entry.
     * 
     * @param filter
     *            The filter to configure.
     * @param initState
     *            Indicates whether the filter is selected by default or not.
     */
    private void addMenuItemFilter(final ProofTreeFilter filter, final boolean initState) {
        final CheckMenuItem cmi = new CheckMenuItem(filter.getContextMenuItemText());
        cmi.setSelected(initState);

        cmi.selectedProperty().addListener((observable, oldValue, newValue) -> {
            if (filteringHandler.getFilterStatus(filter) != newValue) {
                filteringHandler.toggleFilteringStatus(filter);
            }
        });
        getItems().add(cmi);
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

    /**
     * Adds the filter entries to the context menu.
     */
    private void addMenuItemsFilter() {
        for (final Entry<ProofTreeFilter, Boolean> entry : filteringHandler.getFiltersMap().entrySet()) {
            addMenuItemFilter(entry.getKey(), entry.getValue());
        }
    }

    /**
     * Adds a separator to the context menu.
     */
    private void addSeparator() {
        getItems().add(new SeparatorMenuItem());
    }

    /**
     * Adds the entry "Filter by text" to the context menu.
     */
    private void addMenuItemTextFilter() {
        final MenuItem mIFilter = new MenuItem(LBL_FILTER);
        getItems().add(mIFilter);
        mIFilter.setAccelerator(KeyCombination.keyCombination("Ctrl+G"));
        mIFilter.setOnAction(event -> treeViewController.openFilterView());
    }

}
