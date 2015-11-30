package de.uka.ilkd.key.nui.components;

import java.io.File;
import java.util.Iterator;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.fxml.FXML;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

/**
 * controller for the treeView GUI element to visualize proofs
 */
public class TreeViewController {

	@FXML
	private TreeView<String> proofTreeView;

	// defines the width and height of an icon
	private static int iconSize = 15;

	/**
	 * Initialization method for scene, displays the default proof
	 */
	public void initialize() {
		Proof p = loadProof("example01.proof");
		System.out.println("Default proof loaded.");
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
		TreeItem<String> fxRoot = new TreeItem<String>("proof tree");
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
	private void addPNodeToFXNode(Node proofNode, TreeItem<String> fxParent) {
		// create an fxNode and add it to the fxparent
		String nodeName = proofNode.serialNr() + ": " + proofNode.name();
		TreeItem<String> fxNode = new TreeItem<String>(nodeName);
		fxParent.getChildren().add(fxNode);

		// determine number of children and add all children recursively
		int numChildren = proofNode.childrenCount();
		if (numChildren == 0) {
			setNodeIcon(fxNode);
		} else if (numChildren == 1) {
			setNodeIcon(fxParent);
			// add child's subtree to parent
			addPNodeToFXNode(proofNode.child(0), fxParent);
		} else if (numChildren > 1) {
			// for each child create a branch node and add it to the fxparent
			for (Iterator<Node> childrenIterator = proofNode.childrenIterator(); childrenIterator.hasNext();) {
				// get next child
				Node child = childrenIterator.next();

				// define branch label for new node, create node and set icon
				String branchLabel = child.getNodeInfo().getBranchLabel();
				if (branchLabel == null) {
					branchLabel = "Case " + (child.parent().getChildNr(child) + 1);
				}
				TreeItem<String> branch = new TreeItem<String>(branchLabel);
				setNodeIcon(branch);
				
				// add node to parent
				fxParent.getChildren().add(branch);
				
				// call function recursively with current child
				addPNodeToFXNode(child, branch);
			}
		}
	}
	
	/**
	 * Sets an Icon on a given treeItem based on the treeItem's text
	 * 
	 * @param treeItem
	 * 			The tree item where the graphics should be placed on
	 */
	private void setNodeIcon(TreeItem<String> treeItem) {
		String lbl = treeItem.toString().toLowerCase();
		if (lbl.contains("closed goal")) {
			treeItem.setGraphic(IconFactory.keyHoleClosed(iconSize, iconSize));
		} else if (lbl.contains("open goal")) {
			treeItem.setGraphic(IconFactory.keyHole(iconSize, iconSize));
		} else if (lbl.contains("case")) {
			treeItem.setGraphic(IconFactory.keyFolderGray(iconSize, iconSize));
		} else if (lbl.contains("cut")) {
			treeItem.setGraphic(IconFactory.keyFolderBlue(iconSize, iconSize));
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
		File proofFile = new File("resources//de/uka//ilkd//key//examples//" + proofFileName);
		try {
			KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null,
					null, true);
			Proof proof = environment.getLoadedProof();

			return proof;
		} catch (ProblemLoaderException e) {
			e.printStackTrace();
			return null;
		}
	}
}
