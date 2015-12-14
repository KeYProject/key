package de.uka.ilkd.key.nui.components;

import java.io.File;
import java.util.Iterator;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
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

    private Proof p;

    /**
     * Initialization method for scene, displays the default proof
     */
    public void initialize() {
        // add css file to view
        String cssPath = this.getClass().getResource("treeView.css")
                .toExternalForm();
        proofTreeView.getStylesheets().add(cssPath);

        // load and display proof
        Proof p = loadProof("gcd.twoJoins.proof");
        displayProof(p);
    }

    /**
     * shows a proof in the treeView
     * 
     * @param p
     *            the proof to display
     */
    public void displayProof(Proof p) {
        // get the root node
        Node pRoot = p.root();

        // convert proof to fxtree
        TreeItem<Label> fxRoot = new TreeItem<Label>(new Label("proof tree"));
        fxRoot.setExpanded(true);
        addPNodeToFXNode(pRoot, fxRoot);

        // display tree
        proofTreeView.setRoot(fxRoot);
    }

    /**
     * converts a proof node to an fxnode recursively and adds it to an fxparent
     * 
     * @param proofNode
     *            the proof node which should be converted into an fxtree
     * @param fxParent
     *            the node where the converted proofNode should be added to
     */
    private void addPNodeToFXNode(Node proofNode, TreeItem<Label> fxParent) {
        // create an fxNode and add it to the fxparent
        String nodeName = proofNode.serialNr() + ": " + proofNode.name();

        Label label = new Label(nodeName);
        
        // create fx:id
        label.setId(String.valueOf(proofNode.serialNr()));
        
        TreeItem<Label> fxNode = new TreeItem<Label>(label);

        // TreeItem<Label> fxNode = new TreeItem<Label>(new Label(nodeName));

        fxParent.getChildren().add(fxNode);

        // determine number of children and add all children recursively
        int numChildren = proofNode.childrenCount();
        if (numChildren == 0) {
            setNodeIcon(proofNode, fxNode);
        }
        else if (numChildren == 1) {
            setNodeIcon(proofNode, fxParent);
            // add child's subtree to parent
            addPNodeToFXNode(proofNode.child(0), fxParent);
        }
        else if (numChildren > 1) {
            // for each child create a branch node and add it to the fxparent
            for (Iterator<Node> childrenIterator = proofNode
                    .childrenIterator(); childrenIterator.hasNext();) {
                // get next child
                Node child = childrenIterator.next();

                // define branch label for new node, create node and set icon
                String branchLabel = child.getNodeInfo().getBranchLabel();
                if (branchLabel == null) {
                    branchLabel = "Case "
                            + (child.parent().getChildNr(child) + 1);
                }
                System.out.println("label: " + branchLabel);
                System.out.println("#children: " + child.childrenCount());
                System.out.println("isClosed: " + child.isClosed());
                System.out.println("isLeaf: " + child.leaf());
                if (p.getGoal(child) != null) {
                    System.out.println(
                            "isLinked: " + p.getGoal(child).isLinked());
                    System.out.println("isAutomatic: "
                            + p.getGoal(child).isAutomatic() + "\n");
                }
                else {
                    System.out.println("\n");
                }

                Label bLabel = new Label(branchLabel);
                
                // create fx:id
                String id = branchLabel.replace(' ', '_');
                bLabel.setId(id);
             
                TreeItem<Label> branch = new TreeItem<Label>(bLabel);
                setNodeIcon(child, branch);
                branch.getValue().getStyleClass().add("branch");

                // add node to parent
                fxParent.getChildren().add(branch);

                // call function recursively with current child
                addPNodeToFXNode(child, branch);
            }
        }
    }

    /**
     * Sets an Icon on a given treeItem based on the information gathered from
     * the proofNode
     * 
     * @param proofNode
     *            The node item which contains the information to determine the
     *            right icon
     * @param treeItem
     *            The tree item where the graphics should be placed on
     */
    private void setNodeIcon(Node proofNode, TreeItem<Label> treeItem) {
        // node is not a leaf
        if (!(proofNode.leaf())) {
            if (proofNode.isClosed()) {
                // all goals below this node are closed
                treeItem.setGraphic(
                        IconFactory.getKeyClosedInnerNode(iconSize, iconSize));
                return;
            }
            else {
                class FindGoalVisitor implements ProofVisitor {
                    private boolean isLinked = false;

                    public boolean isLinked() {
                        return this.isLinked;
                    }

                    public void visit(Proof proof, Node visitedNode) {
                        Goal g;
                        if ((g = proof.getGoal(visitedNode)) != null
                                && g.isLinked()) {
                            this.isLinked = true;
                        }
                    }
                }
                FindGoalVisitor v = new FindGoalVisitor();

                p.breadthFirstSearch(proofNode, v);
                if (v.isLinked()) {
                    treeItem.setGraphic(IconFactory
                            .getKeyLinkedInnerNode(iconSize, iconSize));
                    return;
                }
            }

            treeItem.setGraphic(
                    IconFactory.getKeyOpenInnerNode(iconSize, iconSize));
        }
        // node is a leaf
        else {
            Goal goal = p.getGoal(proofNode);
            if (goal == null || proofNode.isClosed()) {
                treeItem.setGraphic(IconFactory.getKeyClosedGoal(20, 20));
            }
            else {
                if (goal.isLinked()) {
                    treeItem.setGraphic(
                            IconFactory.getKeyLinkedInnerNode(20, 20));
                }
                else if (!goal.isAutomatic()) {
                    treeItem.setGraphic(
                            IconFactory.getKeyInteractiveGoal(20, 20));
                }
                else {
                    treeItem.setGraphic(IconFactory.getKeyOpenGoal(20, 20));
                }
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
            this.p = proof;
            return proof;
        }
        catch (ProblemLoaderException e) {
            e.printStackTrace();
            return null;
        }
    }
}
