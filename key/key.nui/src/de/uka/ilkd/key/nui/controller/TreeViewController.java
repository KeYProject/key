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
import de.uka.ilkd.key.nui.exceptions.NoSearchViewAddedException;
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
public class TreeViewController extends NUIController implements Observer {

    /**
     * The name of the GUI component.
     */
    public static final String NAME = "treeView";

    /**
     * The fxml file name.
     */
    public static final String RESOURCE = "treeView.fxml";

    /**
     * The IconFactory used to create icons for the proof tree nodes.
     */
    private IconFactory icf;

    /**
     * The VBox containing both the TreeView and the Anchor Pane where the
     * Search elements are.
     */
    @FXML
    private VBox treeViewPane;

    /**
     * Includes the Sub-Window for search
     */
    private Pane searchViewPane;
    private SearchViewController searchViewController;

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

    // TODO comments
    private FilteringHandler fh;

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
     * Opens the search View or moves the focus to the search views text field
     * if a search view already exists.
     * 
     * @throws NoSearchViewAddedException
     */
    public final void openSearchView() {
        if (searchViewPane == null || searchViewController == null)
            return;

        searchViewController.initSearch(proofTreeView, proofTreeCells,
                treeViewPane);

        if (!treeViewPane.getChildren().contains(searchViewPane))
            treeViewPane.getChildren().add(searchViewPane);
    }

    /**
     * init() is called by the NUIController constructor
     */
    @Override
    protected void init() {
        icf = new IconFactory(ProofTreeCell.ICON_SIZE, ProofTreeCell.ICON_SIZE);
        fh = new FilteringHandler(dataModel);

        Platform.runLater(() -> {
            // listener for opening search view
            try {
                ((MainViewController) nui.getController("MainView"))
                        .registerKeyListener((e) -> {
                    if ((e.getCode().equals(KeyCode.F) && e.isShortcutDown())
                            && dataModel.getLoadedTreeViewState() != null) {
                        openSearchView();
                    }
                });
            }
            catch (ControllerNotFoundException exception) {
                exception.showMessage();
            }

            // set cell factory for rendering cells
            proofTreeView.setCellFactory((treeItem) -> {
                final ProofTreeCell cell = new ProofTreeCell(icf, fh, this);
                Platform.runLater(() -> registerTreeCell(cell));
                return cell;
            });

            // add CSS file to view
            final String cssPath = this.getClass()
                    .getResource(
                            "../components/" + ProofTreeStyleConstants.CSS_FILE)
                    .toExternalForm();
            proofTreeView.getStylesheets().add(cssPath);
        });

        // register to the data model
        dataModel.addObserver(this);
    }

    @Override
    public void update(Observable o, Object arg) {
        TreeViewState treeViewState = ((DataModel) o)
                .getTreeViewState((String) arg);
        ProofTreeItem treeItem;

        if (treeViewState == null) {
            treeItem = null;
        }
        else {
            treeItem = treeViewState.getTreeItem();
        }
        // update the proofTreeView component in the treeView
        proofTreeView.setRoot(treeItem);
    }

    public void addSearchView(Pane searchViewPane,
            NUIController nuiController) {

        this.searchViewPane = searchViewPane;
        if (nuiController instanceof SearchViewController)
            this.searchViewController = (SearchViewController) nuiController;
    }

    public Set<ProofTreeCell> getProofTreeCells() {
        return this.proofTreeCells;
    }
}
