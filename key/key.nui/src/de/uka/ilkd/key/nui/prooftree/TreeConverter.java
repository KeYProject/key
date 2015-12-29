package de.uka.ilkd.key.nui.prooftree;

import java.util.Iterator;

import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javafx.scene.control.Label;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

public class TreeConverter {
	public TreeView<Label> proofTreeView;

	/**
	 * The root node of the shown tree
	 */
	public NUIBranchNode nuiRoot;

	/**
	 * The size of the icons in the tree
	 */
	public int iconSize;

	/**
	 * Creates a new TreeConverter object
	 * 
	 * @param proofTreeView
	 * 			The reference to the TreeView<Label> object on the GUI
	 * @param iconSize
	 * 			The desired icon size for the icons in the tree
	 */
	public TreeConverter(TreeView<Label> proofTreeView, int iconSize) {
		this.proofTreeView = proofTreeView;
		this.iconSize = iconSize;
	}

	/**
	 * Adds a CSS stylesheet given by its path to the tree
	 * 
	 * @param path
	 * 			The path of the stylesheet to add
	 */
	public void addStylesheet(String path) {
		proofTreeView.getStylesheets().add(path);
	}

	/**
	 * Visualizes the tree by converting the NUITree to a FXTree
	 */
	public void showTree() {
		// Get root node and decorate it (icons, styles, etc.)
		TreeItem<Label> rootNode = new TreeItem<Label>(new Label(nuiRoot.getLabel()));
		decorateNUIBranchNode(nuiRoot, rootNode);
		
		// Convert the NUITree to a FXTree 
		convertNUITreeToFXTree(nuiRoot, rootNode);
		
		// Define the root of the tree
		proofTreeView.setRoot(rootNode);
	}

	/**
	 * Converts a ProofTree given by the root node pRoot to a NUITree,
	 * which is used as an intermediate representation (decorated abstract tree).
	 * 
	 * @param pRoot
	 * 			The root node of the ProofTree
	 */
	public void convertProofToNUI(Node pRoot) {
		// Create a new branch node (as root node) and assign the appropriate label
		nuiRoot = new NUIBranchNode(pRoot);
		assignNUIFields(pRoot, pRoot.proof(), nuiRoot);
		String label = "Proof_Tree";
		nuiRoot.setLabel(label);
		
		// Convert the ProofTree to a NUITree
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
	private void convertProofTreeToNUITree(Node proofNode, NUIBranchNode parent) {
		Proof p = proofNode.proof();
		NUINode newNode;
		// Create NUI node -----------------------------------------------------
		if (proofNode.leaf()) {
			NUILeafNode leafNode = new NUILeafNode(proofNode);
			newNode = leafNode;
		} else {
			NUIInnerNode innerNode = new NUIInnerNode(proofNode);
			newNode = innerNode;
		}
		// Add created node to parent
		parent.addChild(newNode);

		// Set NUI fields ------------------------------------------------------
		assignNUIFields(proofNode, p, newNode);
		newNode.setSerialNumber(String.valueOf(proofNode.serialNr()));

		// Add children of current node proofNode to parent --------------------
		int numChildren = proofNode.childrenCount();
		if (numChildren == 1) {
			convertProofTreeToNUITree(proofNode.child(0), parent);
		} else if (numChildren > 1) {
			// for each child create a branch node and add it to parent
			for (Iterator<Node> childrenIterator = proofNode.childrenIterator(); childrenIterator.hasNext();) {
				// get next child
				Node child = childrenIterator.next();

				// create NUIBranch and set fields
				NUIBranchNode branchNode = new NUIBranchNode(proofNode);
				String branchLabel = child.getNodeInfo().getBranchLabel();
				if (branchLabel == null) {
					int caseNumber = (child.parent().getChildNr(child) + 1);
					branchLabel = "Case " + caseNumber;
				}
				branchNode.setSerialNumber(branchLabel.replace(" ", "_"));
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
	 * Add the required information to the newNode based on the information
	 * given by the proofNode and the proof.
	 * 
	 * @param proofNode
	 *            The proof node used to determine properties of the newNode.
	 * @param proof
	 *            The proof object used to determine properties of the newNode.
	 * @param newNode
	 *            The NUINode object where the information should be added to.
	 */
	private void assignNUIFields(Node proofNode, Proof proof, NUINode newNode) {
		Goal g = proof.getGoal(proofNode);
		if (proofNode.leaf()) {
			if (g != null) {
				// node has a goal
				newNode.setLinked(g.isLinked());
				newNode.setInteractive(!g.isAutomatic());
				newNode.setLinked(g.isLinked());
				newNode.setClosed(proofNode.isClosed());
			} else {
				// node has no open goal -> node must be closed
				newNode.setClosed(true);
			}
		} else {
			// node is not a leaf
			newNode.setClosed(proofNode.isClosed());
			newNode.setInteractive(proofNode.getNodeInfo().getInteractiveRuleApplication());
		}
		// Set parameters which exist at all nodes
		String nodeName = proofNode.serialNr() + ": " + proofNode.name();
		newNode.setLabel(nodeName);
		newNode.setHasNotes(proofNode.getNodeInfo().getNotes() != null);
		newNode.setActive(proofNode.getNodeInfo().getActiveStatement() != null);

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
	private void convertNUITreeToFXTree(NUIBranchNode nuiNode, TreeItem<Label> fxTreeNode) {

		// Assign fx:id to branch node (needed for test purposes)
		fxTreeNode.getValue().setId(nuiNode.getSerialNumber());

		// Convert child nodes recursively into TreeItem<Label> objects
		for (NUINode child : nuiNode.getChildren()) {

			// Assign fx:id to child node (needed for test purposes)
			Label l = new Label(child.getLabel());
			l.setId(child.getSerialNumber());

			TreeItem<Label> fxNode = new TreeItem<Label>(l);
			fxTreeNode.getChildren().add(fxNode);

			// set node decoration based on node type
			if (child instanceof NUIBranchNode) {
				decorateNUIBranchNode(child, fxNode);
			} else if (child instanceof NUIInnerNode) {
				decorateNUIInnerNode(child, fxNode);
			} else if (child instanceof NUILeafNode) {
				decorateNUILeafNode(child, fxNode);
			}

			// set decoration for all nodes
			// ...if the node has notes
			if (child.hasNotes()) {
				fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_NOTES);
			}
			// ...or if the node has an active statement
			else if (child.isActive()) {
				fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_ACTIVE);
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
	 *            The node used to determine the right decoration
	 * @param fxNode
	 *            The node where the decoration is applied to
	 */
	private void decorateNUIInnerNode(NUINode child, TreeItem<Label> fxNode) {
		if (child.isInteractive()) {
			fxNode.setGraphic(IconFactory.getKeyInteractiveInnerNode(iconSize, iconSize));
		}
	}

	/**
	 * Decorates the nodes of type
	 * {@link de.uka.ilkd.key.nui.prooftree.NUIBranchNode} by using the field
	 * information of child. Assigns CSS style classes and icon images.
	 * 
	 * @param child
	 *            The node used to determine the right decoration
	 * @param fxNode
	 *            The node where the decoration is applied to
	 */
	private void decorateNUIBranchNode(NUINode child, TreeItem<Label> fxNode) {
		fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_BRANCH);
		if (child.isClosed()) {
			fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_CLOSED);
			fxNode.setGraphic(IconFactory.getKeyClosedInnerNode(iconSize, iconSize));
		} else {
			fxNode.setGraphic(IconFactory.getKeyOpenInnerNode(iconSize, iconSize));

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
	 *            The node used to determine the right decoration
	 * @param fxNode
	 *            The node where the decoration is applied to
	 */
	private void decorateNUILeafNode(NUINode child, TreeItem<Label> fxNode) {
		fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_LEAF);
		// leaf node is a closed goal
		if (child.isClosed()) {
			fxNode.setGraphic(IconFactory.getKeyClosedGoal(iconSize, iconSize));
			fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_CLOSED);
		} 
		// leaf node is a linked node
		else if (child.isLinked()) {
			fxNode.setGraphic(IconFactory.getKeyLinkedInnerNode(iconSize, iconSize));
			fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_LINKED);
		} 
		// leaf node is an interactive node
		else if (child.isInteractive()) {
			fxNode.setGraphic(IconFactory.getKeyInteractiveGoal(iconSize, iconSize));
			fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_INTERACTIVE);
		} 
		// else: leaf node must be an open goal
		else {
			fxNode.getValue().getStyleClass().add(ProofTreeStyle.CSS_NODE_OPEN);
			fxNode.setGraphic(IconFactory.getKeyOpenGoal(iconSize, iconSize));
		}
	}
}