package de.uka.ilkd.key.nui.prooftree;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

/**
 * This class visualizes a proof tree in a tree view.
 * @author  Patrick Jattke
 * @author  Matthias Schultheis
 * @version 1.1
 */
public class ProofTreeVisualizer {
    
    /**
     * The label used for the root.
     */
    private static final String LBL_ROOT = "Proof Tree";
	
	/**
	 * The fx tree view for displaying the NUI tree.
	 */
	private final TreeView<NUINode> proofTreeView;

	/**
	 * The root node of the NUI tree.
	 */
	private NUIBranchNode nuiRoot;
	
	/**
	 * A list of leafs that are marked as linked.
	 */
	private List<NUINode> linkedLeafs;

	/**
	 * Creates a new TreeConverter object.
	 *
	 * @param proofTreeView
	 * 			The reference to the TreeView<NUINode> object on the GUI
	 */
	public ProofTreeVisualizer(final TreeView<NUINode> proofTreeView) {
		this.proofTreeView = proofTreeView;
	}

	/**
	 * Adds a CSS stylesheet given by its path to the tree.
	 *
	 * @param path
	 * 			The path of the stylesheet to add
	 */
	public final void addStylesheet(final String path) {
		proofTreeView.getStylesheets().add(path);
	}
	
	private final void visualizeProofTree(NUIBranchNode root) {
	    if (root == null) {
	        throw new IllegalStateException("No proof loaded.");
	    }

	    // create fx root node
	    final TreeItem<NUINode> rootNode = new TreeItem<NUINode>(root);

	    // convert the NUITree to a FXTree 
	    convertNUITreeToFXTree(root, rootNode);

	    // define the root of the tree
	    proofTreeView.setRoot(rootNode);
	}

	/**
	 * Visualizes the loaded proof tree in the proof tree view
	 * by creating tree items.
	 * @throws IllegalStateException in case that no proof was loaded before
	 */
	public final void visualizeProofTree() {
		visualizeProofTree(nuiRoot);
	}
	
	/*public void visualizeFilteredProofTree() {
	    NUINode st = FilteringHandler.getMatchedSubtree(nuiRoot, "LINKED");
	    if(st != null) {
	        visualizeProofTree((NUIBranchNode) st);
	    }
	    else {
	        System.out.println("Fehler");
	    }
	}*/

	/**
	 * loads a proof tree by converting it to a NUITree which 
	 * is used as an intermediate representation 
	 * (decorated abstract tree).
	 *
	 * @param proof The proof tree to load
	 */
	public final void loadProofTree(final Proof proof) {
		final Node pRoot = proof.root();
		
		// Create a new branch node (as root node) and 
		// assign the appropriate label
		nuiRoot = new NUIBranchNode(pRoot);
		assignNUIFields(pRoot, pRoot.proof(), nuiRoot);
		nuiRoot.setLabel(LBL_ROOT);
		
		// reset linked leafs
		linkedLeafs = new LinkedList<NUINode>();
		
		// Convert recursively the ProofTree to a NUITree
		addProofTreeToNUITree(pRoot, nuiRoot);
		
		// set linked leafs
		for (final NUINode linkedLeaf : linkedLeafs) {
		    setNUINodeLinkedTrue(linkedLeaf);
		}
	}

	/**
	 * Converts a proof tree to an NUITree and adds it as child to the given 
	 * NUITree parent.
	 * This works by converting the given node, adding it to the parents, 
	 * and recursively calling itself with the children.
     * The linked field will be not set because it needs the full tree to
     * work properly. Linked leafs will be put into the field 'linkedLeafs'.
     * Please empty the field 'linkedLeafs' before calling and call the
     * method setNUINodeLinkedTrue afer
	 * 
	 * @param proofNode {@link de.uka.ilkd.key.proof.Node}
	 *            the proof tree root node for the tree to add to the NUITree
	 * @param parent {@link de.uka.ilkd.key.nui.NUI.prooftree.NUINode}
	 *            the node where the converted proof tree should be added to
	 */
	private void addProofTreeToNUITree(final Node proofNode, 
			final NUIBranchNode parent) {
		final Proof proof = proofNode.proof();
		NUINode newNode;
		// Create NUI node -----------------------------------------------------
		if (proofNode.leaf()) {
			final NUILeafNode leafNode = new NUILeafNode(proofNode);
			newNode = leafNode;
		} else {
			final NUIInnerNode innerNode = new NUIInnerNode(proofNode);
			newNode = innerNode;
		}
		// Add created node to parent
		parent.addChild(newNode);
		newNode.setParent(parent);

		// Set NUI fields ------------------------------------------------------
		assignNUIFields(proofNode, proof, newNode);
		newNode.setSerialNumber(String.valueOf(proofNode.serialNr()));

		// Add children of current node proofNode to parent --------------------
		final int numChildren = proofNode.childrenCount();
		if (numChildren == 1) {
			addProofTreeToNUITree(proofNode.child(0), parent);
		} else if (numChildren > 1) {
			// for each child create a branch node and add it to parent
			for (final Iterator<Node> childrenIterator = proofNode.childrenIterator();
					childrenIterator.hasNext();) {
				// get next child
				final Node child = childrenIterator.next();

				// create NUIBranch and set fields
				final NUIBranchNode branchNode = new NUIBranchNode(proofNode);
				String branchLabel = child.getNodeInfo().getBranchLabel();
				if (branchLabel == null) {
					final int caseNumber = (child.parent().getChildNr(child) + 1);
					branchLabel = "Case " + caseNumber;
				}
				branchNode.setSerialNumber(branchLabel.replace(" ", "_"));
				branchNode.setLabel(branchLabel);
				branchNode.setClosed(child.isClosed());

				// add node to parent
				parent.addChild(branchNode);
				branchNode.setParent(parent);

				// call function recursively with current child
				addProofTreeToNUITree(child, branchNode);
			}
		}
	}

	/**
	 * Add the required information to the newNode based on the information
	 * given by the proofNode and the proof.
	 * The linked field will be not set because it needs the full tree to
	 * work properly. Linked leafs will be put into the field 'linkedLeafs'.
	 * 
	 * @param proofNode
	 *            The proof node used to determine properties of the newNode.
	 * @param proof
	 *            The proof object used to determine properties of the newNode.
	 * @param newNode
	 *            The NUINode object where the information should be added to.
	 */
	private void assignNUIFields(final Node proofNode, final Proof proof, 
			final NUINode newNode) {
		final Goal goal = proof.getGoal(proofNode);
		if (proofNode.leaf()) {
		    if (goal == null) {
		        // node has no open goal -> node must be closed
                newNode.setClosed(true);
		    } else {
		        // node has a goal
                newNode.setClosed(proofNode.isClosed());
                newNode.setInteractive(!goal.isAutomatic());
                
                if (goal.isLinked()) {
                    linkedLeafs.add(newNode);
                }
		    }
		} else {
			// node is not a leaf
			newNode.setClosed(proofNode.isClosed());
			newNode.setInteractive(proofNode.getNodeInfo().
					getInteractiveRuleApplication());
		}
		// Set parameters which exist at all nodes
		final String nodeName = proofNode.serialNr() + ": " + proofNode.name();
		newNode.setLabel(nodeName);
		newNode.setHasNotes(proofNode.getNodeInfo().getNotes() != null);
		newNode.setActive(proofNode.getNodeInfo().getActiveStatement() != null);
	}

	/**
	 * Sets for a node the field interactive = true and propagates this.
	 * information to its parents.
	 * This method should be called only if the full NUITree was created.
	 * Otherwise it will work not correctly.
	 * @param newNode the node for that interactive should be set true
	 */
	private void setNUINodeLinkedTrue(final NUINode newNode) {
		newNode.setLinked(true);
		
		// propagate linked information to parent
		final NUINode parent = newNode.getParent();
        if (parent != null && parent instanceof NUIBranchNode) {
            final NUIBranchNode parentBranch = (NUIBranchNode) parent;
            if (parentBranch.hasOnlyLinkedBranchChildren()) {
                // if parent has only linked branch children, mark as linked.
                setNUINodeLinkedTrue(parentBranch);
            }
        }
	}

	/**
	 * Converts the root branch of a tree from type
	 * {@link de.uka.ilkd.key.nui.proofTree.Node}, a so called NUITree, to a
	 * FXTree. The FXTree consists of TreeItem<NUINode> which are decorated 
	 * based on the information gathered from the NUITree.
	 * 
	 * The method creates TreeItem<NUINode> objects for each child of nuiNode 
	 * and decorates them based on the information in their respective NUINode
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
	private void convertNUITreeToFXTree(final NUIBranchNode nuiNode, 
			final TreeItem<NUINode> fxTreeNode) {

		// Convert child nodes recursively into TreeItem<Label> objects
		for (final NUINode child : nuiNode.getChildren()) {

			final TreeItem<NUINode> fxNode = new TreeItem<NUINode>(child);
			fxTreeNode.getChildren().add(fxNode);

			// if child is of type branch node -> add children recursively
			if (child instanceof NUIBranchNode) {
				final NUIBranchNode childBranch = (NUIBranchNode) child;
				convertNUITreeToFXTree(childBranch, fxNode);
			}
		}
	}
	
	/**
	 * Returns the root node of the NUITree generated by this class.
	 * 
	 * @return the NUIBranchNode (root) of the tree.
	 */
	public final NUIBranchNode getRootNode() {
	    return this.nuiRoot;
	}
}