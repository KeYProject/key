package de.uka.ilkd.key.nui.prooftree;

import java.util.Iterator;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

/**
 * This class visualizes a proof tree in a tree view
 * @author  Patrick Jattke
 * @author  Matthias Schultheis
 * @version 1.1
 */
public class ProofTreeVisualizer {
	
	/**
	 * the fx tree view for displaying the NUI tree
	 */
	private TreeView<NUINode> proofTreeView;

	/**
	 * the root node of the NUI tree
	 */
	private NUIBranchNode nuiRoot;

	/**
	 * Creates a new TreeConverter object
	 * 
	 * @param proofTreeView
	 * 			The reference to the TreeView<NUINode> object on the GUI
	 */
	public ProofTreeVisualizer(TreeView<NUINode> proofTreeView) {
		this.proofTreeView = proofTreeView;
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
	 * Visualizes the loaded proof tree in the proof tree view
	 * by creating tree items
	 * @throws IllegalStateException in case that no proof was loaded before
	 */
	public void visualizeProofTree() {
		if(nuiRoot == null)
			throw new IllegalStateException("No proof loaded.");
		
		// create fx root node
		TreeItem<NUINode> rootNode = new TreeItem<NUINode>(nuiRoot);
		
		// convert the NUITree to a FXTree 
		convertNUITreeToFXTree(nuiRoot, rootNode);
		
		// define the root of the tree
		proofTreeView.setRoot(rootNode);
	}

	/**
	 * loads a ProofTree given by the root node pRoot by converting
	 * it to a NUITree which is used as an intermediate representation 
	 * (decorated abstract tree).
	 * 
	 * @param pRoot
	 * 			The root node of the ProofTree
	 */
	public void loadProofTree(Proof p) {
		Node pRoot = p.root();
		
		// Create a new branch node (as root node) and assign the appropriate label
		nuiRoot = new NUIBranchNode(pRoot);
		assignNUIFields(pRoot, pRoot.proof(), nuiRoot);
		String label = "Proof_Tree"; //TODO
		nuiRoot.setLabel(label);
		
		// Convert recursively the ProofTree to a NUITree
		addProofTreeToNUITree(pRoot, nuiRoot);
	}

	/**
	 * Converts a proof tree to an NUITree and adds it as child to the given 
	 * NUITree parent.
	 * This works by converting the given node, adding it to the parents, 
	 * and recursively calling itself with the children.
	 * 
	 * @param proofNode {@link de.uka.ilkd.key.proof.Node}
	 *            the proof tree root node for the tree to add to the NUITree
	 * @param parent {@link de.uka.ilkd.key.nui.NUI.prooftree.NUINode}
	 *            the node where the converted proof tree should be added to
	 */
	private void addProofTreeToNUITree(Node proofNode, NUIBranchNode parent) {
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
			addProofTreeToNUITree(proofNode.child(0), parent);
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
				addProofTreeToNUITree(child, branchNode);
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

		// TODO: Implement logic for linked (non-leaf) Nodes
		// see ProofTreeView (line 712-735)
	}

	/**
	 * Converts the root branch of a tree from type
	 * {@link de.uka.ilkd.key.nui.proofTree.Node}, a so called NUITree, to a
	 * FXTree. The FXTree consists of TreeItem<NUINode> which are decorated based
	 * on the information gathered from the NUITree.
	 * 
	 * The method creates TreeItem<NUINode> objects for each child of nuiNode and
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
	private void convertNUITreeToFXTree(NUIBranchNode nuiNode, TreeItem<NUINode> fxTreeNode) {

		// Assign fx:id to branch node (needed for test purposes)
		//TODO what test?
		//fxTreeNode.getValue().setId(nuiNode.getSerialNumber());

		// Convert child nodes recursively into TreeItem<Label> objects
		for (NUINode child : nuiNode.getChildren()) {

			// Assign fx:id to child node (needed for test purposes)
			//TODO what test?
			//NUINode l = new NUINode(child);
			//Label l = new Label(child.getLabel());
			//l.setId(child.getSerialNumber());

			TreeItem<NUINode> fxNode = new TreeItem<NUINode>(child);
			fxTreeNode.getChildren().add(fxNode);

			// if child is of type branch node -> add children recursively
			if (child instanceof NUIBranchNode) {
				NUIBranchNode childBranch = (NUIBranchNode) child;
				convertNUITreeToFXTree(childBranch, fxNode);
			}
		}
	}


}