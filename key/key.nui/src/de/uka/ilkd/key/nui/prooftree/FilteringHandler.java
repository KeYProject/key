package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedList;
import java.util.Optional;

import de.uka.ilkd.key.nui.ComponentFactory;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.TextField;
import javafx.scene.layout.AnchorPane;
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
    final private AnchorPane filterViewAnchorPane;
    
    /**
     * The text field for entering the filter query.
     */
    private TextField filterTextField;
    
    /**
     * The button used to execute filtering.
     */
    private Button btnExecFiltering;
    
    /**
     * Initializes the filtering handler.
     * @param ptv the proofTreeVisualizer
     * @param mainVBox the VBox containing the proof tree
     */
    public FilteringHandler(final ProofTreeVisualizer ptv, final VBox mainVBox) {

        this.ptVisualizer = ptv;
        this.mainVBox = mainVBox;
        
        // get filter view pane
        filterViewAnchorPane = (AnchorPane) (new ComponentFactory("components/"))
                .createComponent(".filterView", ".filterView.fxml");
              
        // get GUI components and register listeners
        final Optional<Node> nodeBtnOk = getNodeChildById(filterViewAnchorPane, "btnFilterOK");
        if (nodeBtnOk.isPresent()) {
            btnExecFiltering = (Button) nodeBtnOk.get();
            btnExecFiltering.setOnAction((event) -> execFiltering());
        }
        else {
            throw new IllegalStateException("Button of filtering view not found!");
        }
        
        final Optional<Node> nodeTFFiltering = getNodeChildById(filterViewAnchorPane, "filterTextField");
        if (nodeTFFiltering.isPresent()) {
            filterTextField = (TextField) nodeTFFiltering.get();
            btnExecFiltering.setOnAction((event) -> execFiltering());
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
            filterTextField.requestFocus();
        }
        else {
            // add filter view to tree view
            mainVBox.getChildren().add(filterViewAnchorPane);
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
            mainVBox.getChildren().remove(filterViewAnchorPane);
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
        
        final String filterQuery = filterTextField.getText().trim();
        
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
