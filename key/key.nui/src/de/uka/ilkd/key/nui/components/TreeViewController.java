package de.uka.ilkd.key.nui.components;

import java.io.File;
import java.util.Iterator;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.nui.prooftree.*;
import javafx.fxml.FXML;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.control.Label;

/**
 * controller for the treeView GUI element to visualize proofs
 */
public class TreeViewController {

    @FXML
    private TreeView<Label> proofTreeView;

    /**
     * The width and height of the icons used in the proofView
     */
    private static int iconSize = 15;

    /**
     * The root node of the shown tree
     */
    private NUIBranchNode nuiRoot;

    /**
     * Initialization method for scene; loads the default proof
     */
    public void initialize() {
        // add CSS file to view
        String cssPath = this.getClass().getResource("treeView.css")
                .toExternalForm();
        proofTreeView.getStylesheets().add(cssPath);

        // load and display proof
        Proof p = loadProof("gcd.twoJoins.proof");
        displayProof(p);
    }

    /**
     * Visualizes the given proof in the treeView
     * 
     * @param proof
     *            The proof which should be shown into the treeView
     */
    public void displayProof(Proof proof) {
        setProof(proof);
        displayProof();
    }

    /**
     * Visualizes the proof which has been set before by {@link #setProof}
     */
    public void displayProof() {
        TreeItem<Label> root = new TreeItem<Label>(
                new Label(nuiRoot.getLabel()));
        decorateNUIBranchNode(nuiRoot, root);
        convertNUITreeToFXTree(nuiRoot, root);
        proofTreeView.setRoot(root);
    }

    /**
     * Assigns an existing proof p to the TreeView and generates an internal
     * intermediate representation (NUITree)
     * 
     * @param proof
     *            The proof file which should be assigned to the TreeView
     */
    public void setProof(Proof proof) {
        // get the root node
        Node pRoot = proof.root();

        // convert proof to NUITree
        nuiRoot = new NUIBranchNode(pRoot);
        nuiRoot.setLabel("Proof Tree");
        nuiRoot.setClosed(pRoot.isClosed()); // TODO refactor
        convertProofTreeToNUITree(pRoot, nuiRoot);
    }

    /**
     * Converts the root proofNode of a tree from type
     * {@link de.uka.ilkd.key.proof.Node} to an NUITree. The NUITree consists of
     * subtypes of {@link de.uka.ilkd.key.nui.NUI.prooftree.NUINode}. These
     * classes contain all decoration information necessary to create an JavaFX
     * Tree (fxtree) by {@link #addNUINodeToFXNode}.
     * </p>
     * 
     * The method adds all children of the given proofNode to the NUIBranchNode
     * and calls then addPNodeToNUINode recursively for each child of type
     * NUIBranchNode.
     * 
     * @param proofNode
     *            the proof node which should be converted into an NUITree
     * @param parent
     *            the node where the converted proof node should be added to
     */
    private void convertProofTreeToNUITree(Node proofNode,
            NUIBranchNode parent) {
        Proof p = proofNode.proof();
        NUINode newNode;
        // Create NUI node -----------------------------------------------------
        if (proofNode.leaf()) {
            NUILeafNode leafNode = new NUILeafNode(proofNode);
            newNode = leafNode;
        }
        else {
            NUIInnerNode innerNode = new NUIInnerNode(proofNode);
            newNode = innerNode;
        }
        // Add created node to parent
        parent.addChild(newNode);

        // Set NUI fields ------------------------------------------------------
        Goal g = p.getGoal(proofNode);
        if (proofNode.leaf()) {
            if (g != null) {
                // node has a goal
                newNode.setLinked(g.isLinked());
                newNode.setInteractive(!g.isAutomatic());
                newNode.setLinked(g.isLinked());
                newNode.setClosed(proofNode.isClosed());
            }
            else {
                // node has no open goal -> node must be closed
                newNode.setClosed(true);
            }
        }
        else {
            // node is not a leaf
            newNode.setClosed(proofNode.isClosed());
            newNode.setInteractive(
                    proofNode.getNodeInfo().getInteractiveRuleApplication());
        }
        // Set parameters which exist at all nodes
        String nodeName = proofNode.serialNr() + ": " + proofNode.name();
        newNode.setLabel(nodeName);
        newNode.setHasNotes(proofNode.getNodeInfo().getNotes() != null);
        newNode.setActive(proofNode.getNodeInfo().getActiveStatement() != null);

        // Add children of current node proofNode to parent --------------------
        int numChildren = proofNode.childrenCount();
        if (numChildren == 1) {
            convertProofTreeToNUITree(proofNode.child(0), parent);
        }
        else if (numChildren > 1) {
            // for each child create a branch node and add it to parent
            for (Iterator<Node> childrenIterator = proofNode
                    .childrenIterator(); childrenIterator.hasNext();) {
                // get next child
                Node child = childrenIterator.next();

                // create NUIBranch and set fields
                NUIBranchNode branchNode = new NUIBranchNode(proofNode);
                String branchLabel = child.getNodeInfo().getBranchLabel();
                if (branchLabel == null) {
                    int caseNumber = (child.parent().getChildNr(child) + 1);
                    branchLabel = "Case " + caseNumber;
                }
                branchNode.setLabel(branchLabel);
                branchNode.setClosed(child.isClosed());

                // add node to parent
                parent.addChild(branchNode);

                // call function recursively with current child
                convertProofTreeToNUITree(child, branchNode);
            }
        }
    }

    /**
     * Converts the root branch of a tree from type
     * {@link de.uka.ilkd.key.nui.proofTree.Node}, a so called NUITree, to a
     * FXTree. The FXTree consists of TreeItem<Labels> which are decorated based
     * on the information gathered from the NUITree.
     * </p>
     * 
     * The method creates TreeItem<Label> objects for each child of nuiNode and
     * decorates them based on the information in their respective NUINode
     * object. If any of the children is of type NUIBranchNode, the method is
     * called again recursively.
     * 
     * @param nuiNode
     *            The node of the NUITree which contains the children to be
     *            added to fxTreeNoe
     * @param fxTreeNode
     *            The node used to append the children
     * 
     */
    private void convertNUITreeToFXTree(NUIBranchNode nuiNode,
            TreeItem<Label> fxTreeNode) {
        for (NUINode child : nuiNode.getChildren()) {
            TreeItem<Label> fxNode = new TreeItem<Label>(
                    new Label(child.getLabel()));
            fxTreeNode.getChildren().add(fxNode);

            // set node decoration based on node type
            if (child instanceof NUIBranchNode) {
                decorateNUIBranchNode(child, fxNode);
            }
            else if (child instanceof NUIInnerNode) {
                decorateNUIInnerNode(child, fxNode);
            }
            else if (child instanceof NUILeafNode) {
                decorateNUILeafNode(child, fxNode);
            }

            // set decoration for all nodes
            // ...if the node has notes
            if (child.hasNotes()) {
                fxNode.getValue().getStyleClass()
                        .add(ProofTreeStyle.CSS_NODE_NOTES);
            }
            // ...or if the node has an active statement
            else if (child.isActive()) {
                fxNode.getValue().getStyleClass()
                        .add(ProofTreeStyle.CSS_NODE_ACTIVE);
            }

            // if child is of type branch node -> add children recursively
            if (child instanceof NUIBranchNode) {
                NUIBranchNode childBranch = (NUIBranchNode) child;
                convertNUITreeToFXTree(childBranch, fxNode);
            }
        }
    }

    /**
     * Decorates the nodes of type
     * {@link de.uka.ilkd.key.nui.prooftree.NUIInnerNode} by using the field
     * information of child. Assigns CSS style classes and icon images.
     * 
     * @param child
     *          The node used to determine the right decoration
     * @param fxNode
     *          The node where the decoration is applied to
     */
    private void decorateNUIInnerNode(NUINode child, TreeItem<Label> fxNode) {
        if (child.isInteractive()) {
            fxNode.setGraphic(
                    IconFactory.getKeyInteractiveInnerNode(iconSize, iconSize));
        }
    }

    /**
     * Decorates the nodes of type
     * {@link de.uka.ilkd.key.nui.prooftree.NUIBranchNode} by using the field
     * information of child. Assigns CSS style classes and icon images.
     * 
     * @param child
     *          The node used to determine the right decoration
     * @param fxNode
     *          The node where the decoration is applied to
     */
    private void decorateNUIBranchNode(NUINode child, TreeItem<Label> fxNode) {
        fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_BRANCH);
        if (child.isClosed()) {
            fxNode.getValue().getStyleClass()
                    .add(ProofTreeStyle.CSS_NODE_CLOSED);
            fxNode.setGraphic(
                    IconFactory.getKeyClosedInnerNode(iconSize, iconSize));
        }
        else {
            fxNode.setGraphic(
                    IconFactory.getKeyOpenInnerNode(iconSize, iconSize));

        }
        // TODO: Implement logic for linked (non-leaf) Nodes
        // see ProofTreeView (line 712-735)
    }

    /**
     * Decorates the nodes of type
     * {@link de.uka.ilkd.key.nui.prooftree.NUILeafNode} by using the field
     * information of child. Assigns CSS style classes and icon images.
     * 
     * @param child
     *          The node used to determine the right decoration
     * @param fxNode
     *          The node where the decoration is applied to
     */
    private void decorateNUILeafNode(NUINode child, TreeItem<Label> fxNode) {
        fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_LEAF);
        if (child.isClosed()) {
            fxNode.setGraphic(IconFactory.getKeyClosedGoal(iconSize, iconSize));
            fxNode.getValue().getStyleClass()
                    .add(ProofTreeStyle.CSS_NODE_CLOSED);
        }
        else if (child.isLinked()) {
            fxNode.setGraphic(
                    IconFactory.getKeyLinkedInnerNode(iconSize, iconSize));
            fxNode.getValue().getStyleClass()
                    .add(ProofTreeStyle.CSS_NODE_LINKED);
        }
        else if (child.isInteractive()) {
            fxNode.setGraphic(
                    IconFactory.getKeyInteractiveGoal(iconSize, iconSize));
            fxNode.getValue().getStyleClass()
                    .add(ProofTreeStyle.CSS_NODE_INTERACTIVE);
        }
        else {
            fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_OPEN);
            fxNode.setGraphic(IconFactory.getKeyOpenGoal(iconSize, iconSize));
        }
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    private Proof loadProof(String proofFileName) {
        String examplesRoot = "resources//de/uka//ilkd//key//examples//";
        File proofFile = new File(examplesRoot + proofFileName);
        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFile, null, null,
                    null, true);
            Proof proof = environment.getLoadedProof();
            return proof;
        }
        catch (ProblemLoaderException e) {
            e.printStackTrace();
            return null;
        }
    }
}
