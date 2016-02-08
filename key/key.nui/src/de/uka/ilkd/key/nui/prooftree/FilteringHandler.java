package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedList;
import java.util.Optional;

import de.uka.ilkd.key.nui.ComponentFactory;
import de.uka.ilkd.key.nui.IconFactory;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;

/**
 * Performs the filtering.
 * @author Matthias Schultheis
 * @version 1.0
 *
 */
public class FilteringHandler {
    
    /**
     * The visualizer used for displaying the filtered tree.
     */
    private ProofTreeVisualizer ptVisualizer;
    
    /**
     * Contains the visibility state of the filtering view.
     */
    private boolean filteringPaneIsVisible = false;
    
    /**
     * The VBox containing both the TreeView and the Anchor Pane where the
     * Search elements are.
     */
    private VBox mainVBox;
    
    /**
     * The anchor pane for the filtering view.
     */
    private Pane filterViewPane;
    
    /**
     * The text field for entering the filter query.
     */
    private TextField tfFilterQuery;
    
    /**
     * The button used to execute filtering.
     */
    private ToggleButton btnFilteringActive;
    
    /**
     * Initializes the filtering handler.
     * @param ptv the proofTreeVisualizer
     * @param mainVBox the VBox containing the proof tree
     */
    public FilteringHandler(final ProofTreeVisualizer ptv, final VBox mainVBox, final IconFactory icf) {

        this.ptVisualizer = ptv;
        this.mainVBox = mainVBox;
        
        // Loads the components from the .filterView fxml file
        ComponentFactory cf = ComponentFactory.getInstance();
        ComponentFactory.setResourceDirectory("components/");
        
        filterViewPane = (Pane) (cf)
                .createComponent(".filterView", ".filterView.fxml");
                
              
        // get GUI components and register listeners
        final Optional<Node> nodeBtnOk = getNodeChildById(filterViewPane, "btnFilterActve");
        if (nodeBtnOk.isPresent()) {
            btnFilteringActive = (ToggleButton) nodeBtnOk.get();
            btnFilteringActive.setOnAction((event) -> execFiltering());
            btnFilteringActive.setGraphic(icf.getImage("filter.png"));
        }
        else {
            throw new IllegalStateException("Button of filtering view not found!");
        }
        
        final Optional<Node> nodeTFFiltering = getNodeChildById(filterViewPane, "tfFilterQuery");
        if (nodeTFFiltering.isPresent()) {
            tfFilterQuery = (TextField) nodeTFFiltering.get();
        }
        else {
            throw new IllegalStateException("Text field of filtering view not found!");
        }
        
        final Optional<Node> nodeBtnClose = getNodeChildById(filterViewPane, "btnFilterClose");
        if (nodeBtnClose.isPresent()) {
            Button btnClose = (Button) nodeBtnClose.get();
            btnClose.setOnAction((event) -> hideFilteringPane());
            btnClose.setGraphic(icf.getImage("cross.png"));
        }
        else {
            throw new IllegalStateException("Text field of filtering view not found!");
        }
        
        openFilteringPane();
        
    }
    
    /**
     * Opens the filtering pane if it's not visible.
     * Otherwise it requests focus.
     */
    public void openFilteringPane() {
        if (filteringPaneIsVisible) {
            tfFilterQuery.requestFocus();
        }
        else {
            // add filter view to tree view
            mainVBox.getChildren().add(filterViewPane);
            filteringPaneIsVisible = true;
        }
    }
    
    /**
     * Hides the filtering pane.
     */
    public void hideFilteringPane() {
        if (!filteringPaneIsVisible) {
            throw new IllegalStateException("Filtering Pane is already closed.");
        }
        else {
            // remove filter view from tree view
            mainVBox.getChildren().remove(filterViewPane);
            filteringPaneIsVisible = false;
        }
    }
    
    /**
     * Returns the child node of a parent node if it exists.
     * @param parent the parent node
     * @param cid the fx id of the child to return
     * @return the child of parent having the fx id
     */
    private Optional<Node> getNodeChildById(javafx.scene.Parent parent, String cid) {
        final ObservableList<Node> children = parent.getChildrenUnmodifiable();
        return children.stream().filter(n -> n.getId().equals(cid)).findAny();
    }
    
    /**
     * Executes filtering process.
     */
    public void execFiltering() {
        
        final String filterQuery = tfFilterQuery.getText().trim();
        
        if(filterQuery.isEmpty())
            return;
        
        final NUINode filteredTree = getMatchedSubtree(ptVisualizer.getRootNode(), filterQuery);
        
        if(filteredTree != null) {
            ptVisualizer.visualizeProofTree((NUIBranchNode) filteredTree);
        }
        else {
            System.out.println("No matches found.");
        }
        
        //TODO information of AG needed.
        ProofTreeActions.expandAll(ptVisualizer.getProofTreeView().getRoot());
    }
    
    
    /**
     * Returns a subtree consisting of only matching nodes.
     * @param root    the root node of the source tree
     * @param search  the query used for filtering
     * @return        the root node of a filtered tree or null if not found
     */
    public static NUINode getMatchedSubtree(final NUINode root, final String search) {
        // label matches -> copy subtree
        if (matchesFilter(root, search)) {
            //TODO set parent needed
            final NUINode filteredTreeRoot = (NUINode) root.clone();
            
            return filteredTreeRoot;
        }
        // branch nodes -> look at children
        else if (root instanceof NUIBranchNode) {

            
            final LinkedList<NUINode> matchedChildren = new LinkedList<NUINode>();
            final NUIBranchNode rootBN = (NUIBranchNode) root;
            
            // add matching children
            for (final NUINode child : rootBN.getChildren()) {
                final NUINode childMatchedSubTree = getMatchedSubtree(child, search);
                if (childMatchedSubTree != null) {
                    matchedChildren.add(childMatchedSubTree);
                }
            }
            
            // if there are children matches, roots is also indirectly a match
            if (!matchedChildren.isEmpty()) {
                
                final NUIBranchNode filteredRoot = rootBN.cloneWithoutChildren();
                filteredRoot.setChildren(matchedChildren);
                
                // set parent for children
                matchedChildren.forEach((child) -> child.setParent(filteredRoot));
                
                return filteredRoot;
                
            }
            // no children match -> branch doesnt match
            else {
                return null;
            }
        }
        // root doesnt match and is no branch node
        else {
            return null;
        }
    }
    
    /**
     * Checks if a node matches a filter rule.
     * @param node    the node to check
     * @param filter  the filter string
     * @return        true iff the node matches the filter rule
     */
    private static boolean matchesFilter(final NUINode node, final String filter) {
        final String lblLC = node.getLabel().toLowerCase();
        final String filterLC = filter.toLowerCase();
        return lblLC.contains(filterLC);
    }
}
