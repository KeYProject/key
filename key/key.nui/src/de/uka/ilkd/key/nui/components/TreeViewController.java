package de.uka.ilkd.key.nui.components;

import java.io.File;
import java.util.Iterator;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.fxml.FXML;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

/**
 * controller for the treeView gui element to visualize proofs
 */
public class TreeViewController {
	
	@FXML private TreeView<String> proofTreeView;
	
	/**
	 * Initialization method for scene
	 * displays the a default proof
	 */
	public void initialize() {
		Proof p = loadProof("lol.proof");
		
		System.out.println("Default proof loaded.");
		displayProof(p);
	}
	
	/**
	 * shows a proof in the treeView
	 * @param p the proof to display
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
	 * converts a proof node to an fxnode recursively
	 * and adds it to an fx fxparent
	 * @param proofNode
	 * @param fxParent
	 */
	private void addPNodeToFXNode(Node proofNode, TreeItem<String> fxParent) {
		// create an fxNode and add it to the fxparent
		String label = proofNode.serialNr() + ": " + proofNode.name();
		TreeItem<String> fxNode = new TreeItem<String>(label);
		fxParent.getChildren().add(fxNode);
		
		
		// add all children recursively
		int numChildren = proofNode.childrenCount();
		
		if(numChildren == 1) {
			// add child's subtree to parent
			addPNodeToFXNode(proofNode.child(0), fxParent);
		} else if(numChildren > 1) {
			// for each child create a branch node and add it to the fxparent
			for(Iterator<Node> childrenIterator = proofNode.childrenIterator(); childrenIterator.hasNext();) {
				Node child = childrenIterator.next();
				
				String branchLabel = child.getNodeInfo().getBranchLabel();
				TreeItem<String> branch = new TreeItem<String>(branchLabel);
				fxParent.getChildren().add(branch);
				
				addPNodeToFXNode(child, branch);
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
        File proofFile = new File("../"+ proofFileName);

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
