package de.uka.ilkd.key.nui.controller;

import de.uka.ilkd.key.nui.prooftree.FilteringHandler;
import de.uka.ilkd.key.nui.prooftree.NUIBranchNode;
import de.uka.ilkd.key.nui.prooftree.NUILeafNode;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;

/**
 * Controller for handling the text filtering feature.
 * 
 * @author Stefan Pilot
 *
 */
@ControllerAnnotation(createMenu = false)
@SuppressWarnings("PMD.AtLeastOneConstructor")
public class FilterViewController extends NUIController {

    /**
     * The {@link Button} to close the view.
     */
    @FXML
    private transient Button btnCloseView;
    /**
     * The {@link Button} to toggle the filtering.
     */
    @FXML
    private transient ToggleButton btnToggleFilter;
    /**
     * The HBox containing the whole view.
     */
    @FXML
    private transient HBox filterViewHBox;
    /**
     * The text field for putting in the filter query.
     */
    @FXML
    private transient TextField tfFilterQuery;

    /**
     * The filteringHandler to be used for filtering.
     */
    private FilteringHandler filteringHandler;

    /**
     * The term to filter by.
     */
    private String term = "";

    /**
     * The filter to hand over to the {@link FilteringHandler}.
     */
    private final ProofTreeFilter textFilter = new ProofTreeFilter() {

        /**
         * This filter is not meant to be put into any context menu ever.
         */
        @Override
        public String getContextMenuItemText() {
            return "Text filter: '" + term + "'";
        }

        /**
         * Returns false (and by thus makes the filter hide) all nodes that
         * <ol>
         * <li/>are intermediate nodes and
         * <li/>do not contain the filter term.
         * </ol>
         */
        @Override
        @SuppressWarnings("PMD.JUnit4TestShouldUseTestAnnotation")
        public boolean test(final NUINode node) {
            return node instanceof NUIBranchNode || node instanceof NUILeafNode
                    || node.getLabel().toLowerCase().contains(term);
        }

    };

    /**
     * The Pane this FilterView will be drawn into.
     */
    private Pane treeViewPane;

    /**
     * Set up the parameters used for displaying the FilterView and for, well,
     * filtering.
     * 
     * @param filteringHandler
     *            the {@link FilteringHandler} to transfer the filter commands
     *            to.
     * @param treeViewPane
     *            the {@link Pane} to draw the view into.
     */
    public void initializeFiltering(final FilteringHandler filteringHandler,
            final Pane treeViewPane) {
        this.filteringHandler = filteringHandler;
        this.treeViewPane = treeViewPane;
        Platform.runLater(() -> performFocusRequest());
    }

    /**
     * Makes the embedded text field request focus from the application.
     */
    public void performFocusRequest() {
        tfFilterQuery.requestFocus();
    }

    /**
     * Orders the FilterView to hide itself.
     */
    private void closeFilterView() {
        term = "";
        btnToggleFilter.setSelected(false);
        performFiltering();
        treeViewPane.getChildren().remove(filterViewHBox);
    }

    /**
     * Makes the {@link FilteringHandler} filter by the term given into the
     * {@link TextField}, but only if the {@link ToggleButton} is selected.
     */
    public void performFiltering() {
        if (term.isEmpty() || !btnToggleFilter.isSelected()) {
            filteringHandler.stopFilteringBy(textFilter);
        }
        else {
            filteringHandler.filterBy(textFilter);
        }

    }

    @Override
    protected void init() {
        btnCloseView.setOnAction((event) -> closeFilterView());

        btnToggleFilter.setSelected(true);
        btnToggleFilter.selectedProperty().addListener((obs, oldVal, newVal) -> performFiltering());

        tfFilterQuery.textProperty().addListener((obs, oldVal, newVal) -> {
            this.term = newVal.toLowerCase();
            performFiltering();
        });

        filterViewHBox.setOnKeyPressed((event) -> {
            switch (event.getCode()) {
            case ESCAPE:
                closeFilterView();
                break;
            case ENTER:
                btnToggleFilter.setSelected(!btnToggleFilter.isSelected());
                performFiltering();
                break;
            default: // Do nothing
                break;
            }
        });
    }

    /**
     * Getter.
     * @return the {@link FilteringHandler}.
     */
    public FilteringHandler getFilteringHandler() {
        return filteringHandler;
    }
    /**
     * Setter.
     * @param filteringHandler the {@link FilteringHandler}.
     */
    public void setFilteringHandler(final FilteringHandler filteringHandler) {
        this.filteringHandler = filteringHandler;
    }
    /**
     * Getter.
     * @return the {@link String}.
     */
    public String getTerm() {
        return term;
    }
    /**
     * Setter.
     * @param term the {@link String}.
     */
    public void setTerm(final String term) {
        this.term = term;
    }
    /**
     * Getter.
     * @return the treeView{@link Pane}.
     */
    public Pane getTreeViewPane() {
        return treeViewPane;
    }
    /**
     * Setter.
     * @param the treeView{@link Pane}.
     */
    public void setTreeViewPane(final Pane treeViewPane) {
        this.treeViewPane = treeViewPane;
    }
    /**
     * Getter.
     * @return the {@link ProofTreeFilter}.
     */
    public ProofTreeFilter getTextFilter() {
        return textFilter;
    }

}
