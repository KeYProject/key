package de.uka.ilkd.key.nui.controller;

import java.util.Collections;
import java.util.Observable;
import java.util.Observer;
import java.util.Set;
import java.util.WeakHashMap;
import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.prooftree.FilteringHandler;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeCell;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import de.uka.ilkd.key.nui.prooftree.ProofTreeStyleConstants;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.scene.control.TreeView;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;

/**
 * Controller for the treeView GUI element to visualize proofs.
 * 
 * @author Patrick Jattke
 * @author Matthias Schultheis
 * @author Stefan Pilot
 * @author Florian Breitfelder
 * @version 1.1
 */
@ControllerAnnotation(createMenu = true)
@SuppressWarnings("PMD.AtLeastOneConstructor")
public class TreeViewController extends NUIController implements Observer {

    /**
     * Handles the filtering of the proofTree.
     */
    private FilteringHandler filteringHandler;

    /**
     * The IconFactory used to create icons for the proof tree nodes.
     */
    private IconFactory icf;

    /**
     * The tree cells used for displaying tree nodes.
     */
    private final Set<ProofTreeCell> proofTreeCells = Collections
            .newSetFromMap(new WeakHashMap<>());

    /**
     * The proofTree view of the GUI.
     */
    @FXML
    private TreeView<NUINode> proofTreeView;

    /**
     * A reference to the controller associated with the searchView.
     */
    private SearchViewController searchViewController;
    /**
     * Includes the Sub-Window for search.
     */
    private Pane searchViewPane;

    /**
     * The VBox containing both the TreeView and the Anchor Pane where the
     * Search elements are. Includes the Sub-Window for search.
     */
    @FXML
    private VBox treeViewPane;

    /**
     * Adds the given searchViewPane to the TreeViewController and stores a
     * reference to the SearchViewController.
     * 
     * @param searchViewPane
     *            The pane containing the SearchView.
     * @param nuiController
     *            The SearchViewController used to search in the TreeView.
     */
    public void addSearchView(final Pane searchViewPane, final NUIController nuiController) {
        this.searchViewPane = searchViewPane;
        if (nuiController instanceof SearchViewController) {
            this.searchViewController = (SearchViewController) nuiController;
        }
    }

    /**
     * Getter.
     * 
     * @return the {@link FilteringHandler}
     */
    public FilteringHandler getFilteringHandler() {
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
     * Returns a set of all {@link ProofTreeCell} currently display in the
     * TreeView.
     * 
     * @return Set&tl;ProofTreeCell%gt; a set of ProofTreeCells.
     * 
     */
    public Set<ProofTreeCell> getProofTreeCells() {
        return this.proofTreeCells;
    }

    /**
     * Getter.
     * 
     * @return the {@link TreeView}&lt;{@link NUINode}&gt;
     */
    public TreeView<NUINode> getProofTreeView() {
        return proofTreeView;
    }

    /**
     * Getter.
     * 
     * @return the {@link SearchViewController}.
     */
    public SearchViewController getSearchViewController() {
        return searchViewController;
    }

    /**
     * Getter.
     * 
     * @return the {@link SearchViewPane}.
     */
    public Pane getSearchViewPane() {
        return searchViewPane;
    }

    /**
     * Getter.
     * 
     * @return the {@link VBox}.
     */
    public VBox getTreeViewPane() {
        return treeViewPane;
    }

    /**
     * Opens the search View or moves the focus to the search views text field
     * if a search view already exists.
     * 
     * @throws NoSearchViewAddedException
     */
    public final void openSearchView() {

        if (searchViewPane != null || searchViewController != null) {

            searchViewController.initSearch(proofTreeView, proofTreeCells, treeViewPane);

            if (!treeViewPane.getChildren().contains(searchViewPane)) {
                treeViewPane.getChildren().add(searchViewPane);
            }
        }
    }

    private Pane filterViewHBox;
    private FilterViewController filterViewController;

    public final void openFilterView() {
        if (filterViewHBox != null || filterViewController != null) {
            filterViewController.initializeFiltering(filteringHandler, treeViewPane);
            if (!treeViewPane.getChildren().contains(filterViewHBox)) {
                treeViewPane.getChildren().add(filterViewHBox);
            }
        }
    }

    public void addFilterView(final Pane filterViewHBox, final NUIController nuiController) {
        this.filterViewHBox = filterViewHBox;
        if (nuiController instanceof FilterViewController) {
            this.filterViewController = (FilterViewController) nuiController;
        }
    }

    /**
     * Setter.
     * 
     * @param filteringHandler
     *            the {@link FilteringHandler} you want to set.
     */
    public void setFilteringHandler(final FilteringHandler filteringHandler) {
        this.filteringHandler = filteringHandler;
    }

    /**
     * Setter.
     * 
     * @param icf
     *            the {@link IconFactory} you want to set.
     */
    public void setIcf(final IconFactory icf) {
        this.icf = icf;
    }

    /**
     * Setter.
     * 
     * @param proofTreeView
     *            the {@link TreeView}&lt;{@link NUINode}&gt; you want to set.
     */
    public void setProofTreeView(final TreeView<NUINode> proofTreeView) {
        this.proofTreeView = proofTreeView;
    }

    /**
     * Setter.
     * 
     * @param searchViewController
     *            the {@link SearchViewController} you want to set.
     */
    public void setSearchViewController(final SearchViewController searchViewController) {
        this.searchViewController = searchViewController;
    }

    /**
     * Setter.
     * 
     * @param searchViewPane
     *            the{@link Pane} you want to set.
     */
    public void setSearchViewPane(final Pane searchViewPane) {
        this.searchViewPane = searchViewPane;
    }

    /**
     * Setter.
     * 
     * @param treeViewPane
     *            the {@link Pane} you want to set.
     */
    public void setTreeViewPane(final VBox treeViewPane) {
        this.treeViewPane = treeViewPane;
    }

    @Override
    public void update(final Observable obs, final Object arg) {
        if (obs instanceof DataModel) {
            final TreeViewState treeViewState = ((DataModel) obs).getTreeViewState((String) arg);
            final ProofTreeItem treeItem;
            if (treeViewState == null) {
                treeItem = null;
            }
            else {
                treeItem = treeViewState.getTreeItem();
            }

            // update the proofTreeView component in the treeView
            proofTreeView.setRoot(treeItem);
        }
    }

    /**
     * This method should be called every time a new TreeCell is being created.
     * <tt>this</tt> will reference the ProofTreeCell in a WeakHandle in order
     * to find out which TreeItems currently are visible to the user. This is
     * needed because TreeView does not provide something like getTreeCells
     *
     * @param treeCell
     *            the ProofTreeCell to register.
     */
    private void registerTreeCell(final ProofTreeCell treeCell) {
        proofTreeCells.add(treeCell);

    }

    /**
     * init() is called by the NUIController constructor.
     */
    @Override
    protected void init() {
        icf = new IconFactory(ProofTreeCell.ICON_SIZE, ProofTreeCell.ICON_SIZE);
        filteringHandler = new FilteringHandler(getDataModel());

        Platform.runLater(() -> {
            // listener for opening search view
            try {
                ((MainViewController) getNui().getController("MainView"))
                        .registerKeyListener((event) -> {
                    if (event.getCode().equals(KeyCode.F) && event.isShortcutDown()
                            && getDataModel().getLoadedTreeViewState() != null) {
                        openSearchView();
                    }

                    if (event.getCode().equals(KeyCode.G) && event.isShortcutDown()
                            && getDataModel().getLoadedTreeViewState() != null) {
                        openFilterView();
                    }
                    /*
                     * if (event.isShortcutDown() &&
                     * dataModel.getLoadedTreeViewState() != null) { switch
                     * (event.getCode()) { case F: openSearchView(); break; case
                     * G: openFilterView(); break; default: break; } }
                     * 
                     * });
                     */
                });
            }
            catch (ControllerNotFoundException exception) {
                exception.showMessage();
            }

            // set cell factory for rendering cells
            proofTreeView.setCellFactory((treeItem) -> {
                final ProofTreeCell cell = new ProofTreeCell(icf, filteringHandler, this);
                Platform.runLater(() -> registerTreeCell(cell));
                return cell;
            });

            // add CSS file to view
            proofTreeView.getStylesheets()
                    .add("/de/uka/ilkd/key/nui/components/" + ProofTreeStyleConstants.CSS_FILE);
        });

        // register to the data model
        getDataModel().addObserver(this);
    }

}
