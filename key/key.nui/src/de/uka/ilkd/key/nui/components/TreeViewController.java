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

    // defines the width and height of an icon
    private static int iconSize = 15;

    // the current proof object used for the tree
    // private Proof p;

    private NUIBranchNode nuiRoot;

    /**
     * Initialization method for scene, displays the default proof
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

    public void displayProof(Proof proof) {
        setProof(proof);

        displayProof();
    }

    public void displayProof() {
        TreeItem<Label> root = new TreeItem<Label>(
                new Label(nuiRoot.getLabel()));
        // TODO decoration for root node
        addNUINodeToFXNode(nuiRoot, root);
        proofTreeView.setRoot(root);
    }

    public void setProof(Proof p) {
        // get the root node
        Node pRoot = p.root();

        // convert proof to NUITree
        nuiRoot = new NUIBranchNode(pRoot);
        nuiRoot.setLabel("Proof Tree");
        nuiRoot.setClosed(pRoot.isClosed()); // TODO refactor
        addPNodeToNUINode(pRoot, nuiRoot);
    }

    /**
     * converts a proof node to an fxnode recursively and adds it to an fxparent
     * 
     * @param proofNode
     *            the proof node which should be converted into an fxtree
     * @param fxParent
     *            the node where the converted proofNode should be added to
     */
    private void addPNodeToNUINode(Node proofNode, NUIBranchNode parent) {
        Proof p = proofNode.proof();
        NUINode newNode;
        // Create NUI node
        // ----------------------------------------------------------------
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

        // Set NUI fields
        // -----------------------------------------------------------------
        Goal g = p.getGoal(proofNode);
        if (proofNode.leaf()) {
            if (g != null) {
                newNode.setLinked(g.isLinked());
                newNode.setInteractive(!g.isAutomatic());
                newNode.setLinked(g.isLinked());
                newNode.setClosed(proofNode.isClosed());
            }
            else {
                newNode.setClosed(true);
            }
        }
        else {
            newNode.setClosed(proofNode.isClosed());
            newNode.setInteractive(
                    proofNode.getNodeInfo().getInteractiveRuleApplication());
        }
        String nodeName = proofNode.serialNr() + ": " + proofNode.name();
        newNode.setLabel(nodeName);

        newNode.setHasNotes(proofNode.getNodeInfo().getNotes() != null);
        newNode.setActive(proofNode.getNodeInfo().getActiveStatement() != null);

        // Add children of current node proofNode to parent
        // --------------------------------
        int numChildren = proofNode.childrenCount();
        if (numChildren == 1) {
            addPNodeToNUINode(proofNode.child(0), parent);
        }
        else if (numChildren > 1) {
            // for each child create a branch node and add it to the fxparent
            for (Iterator<Node> childrenIterator = proofNode
                    .childrenIterator(); childrenIterator.hasNext();) {
                // get next child
                Node child = childrenIterator.next();

                // create NUIBranch and set fields
                NUIBranchNode branchNode = new NUIBranchNode(proofNode);

                // define branch label for new node, create node and set icon
                String branchLabel = child.getNodeInfo().getBranchLabel();
                if (branchLabel == null) {
                    branchLabel = "Case "
                            + (child.parent().getChildNr(child) + 1);
                }
                branchNode.setLabel(branchLabel);

                branchNode.setClosed(child.isClosed());

                // add node to parent
                parent.addChild(branchNode);

                // call function recursively with current child
                addPNodeToNUINode(child, branchNode);
            }
        }

    }

    // TODO rename, javadoc
    private void addNUINodeToFXNode(NUIBranchNode branch,
            TreeItem<Label> fxParent) {
        for (NUINode child : branch.getChildren()) {
            TreeItem<Label> fxNode = new TreeItem<Label>(
                    new Label(child.getLabel()));
            fxParent.getChildren().add(fxNode);

            // set node decoration
            if (child instanceof NUIBranchNode) {
                fxNode.getValue().getStyleClass()
                        .add(ProofTreeStyle.CSS_NODE_BRANCH);
                if (child.isClosed()) {
                    fxNode.getValue().getStyleClass()
                            .add(ProofTreeStyle.CSS_NODE_CLOSED);
                    fxNode.setGraphic(IconFactory
                            .getKeyClosedInnerNode(iconSize, iconSize));
                }
                else {
                    fxNode.setGraphic(IconFactory.getKeyOpenInnerNode(iconSize,
                            iconSize));

                }
                // TODO: Implement logic for linked (non-leaf) Nodes
                // see ProofTreeView (line 712-735)
            }
            else if (child instanceof NUIInnerNode) {
                if (child.isInteractive()) {
                    fxNode.setGraphic(IconFactory
                            .getKeyInteractiveInnerNode(iconSize, iconSize));
                }
            }
            else if (child instanceof NUILeafNode) {
                fxNode.getValue().getStyleClass()
                        .add(ProofTreeStyle.CSS_NODE_LEAF);
                if (child.isClosed()) {
                    fxNode.setGraphic(
                            IconFactory.getKeyClosedGoal(iconSize, iconSize));
                    fxNode.getValue().getStyleClass()
                            .add(ProofTreeStyle.CSS_NODE_CLOSED);
                }
                else if (child.isLinked()) {
                    fxNode.setGraphic(IconFactory
                            .getKeyLinkedInnerNode(iconSize, iconSize));
                    fxNode.getValue().getStyleClass()
                            .add(ProofTreeStyle.CSS_NODE_LINKED);
                }
                else if (child.isInteractive()) {
                    fxNode.setGraphic(IconFactory
                            .getKeyInteractiveGoal(iconSize, iconSize));
                    fxNode.getValue().getStyleClass()
                            .add(ProofTreeStyle.CSS_NODE_INTERACTIVE);

                }
                else {
                    fxNode.getValue().getStyleClass()
                            .add(ProofTreeStyle.CSS_NODE_OPEN);
                    fxNode.setGraphic(
                            IconFactory.getKeyOpenGoal(iconSize, iconSize));
                }
            }

            if (child.hasNotes()) {
                fxNode.getValue().getStyleClass()
                        .add(ProofTreeStyle.CSS_NODE_NOTES);
            }
            else if (child.isActive()) {
                fxNode.getValue().getStyleClass()
                        .add(ProofTreeStyle.CSS_NODE_ACTIVE);
            }

            // if branch node add children recursively
            if (child instanceof NUIBranchNode) {
                NUIBranchNode childBranch = (NUIBranchNode) child;
                addNUINodeToFXNode(childBranch, fxNode);
            }
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
        File proofFile = new File(
                "resources//de/uka//ilkd//key//examples//" + proofFileName);
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
