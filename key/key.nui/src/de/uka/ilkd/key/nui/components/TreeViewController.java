package de.uka.ilkd.key.nui.components;

import java.io.File;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
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
		System.out.println("init.\nCreate Default Proof.");
		
		//Proof p = getDefaultProof();
		Proof p = loadProof("key.core.test/resources/testcase/join/gcd.closed.proof");
		System.out.println("Default proof created. Now display the proof.");
		
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
		TreeItem<String> nodeAsTI = proofToFxTree(pRoot);
		
		// display tree
		proofTreeView.setRoot(nodeAsTI);
	}
	
	/**
	 * converts a proof to a fxtree
	 * recursively adds children to fxtree
	 * @param pRoot the root of the proof
	 * @return the corresponding fxtree
	 */
	private TreeItem<String> proofToFxTree(Node pRoot) {
		// create a fx tree item with label
		String label = pRoot.serialNr() + ": " + pRoot.name();
		TreeItem<String> fxRoot = new TreeItem<String>(label);
		fxRoot.setExpanded(true);
		
		// add all children recursively
		int numChildren = pRoot.childrenCount();
		for(int i = 0; i < numChildren; i++) {
			// convert subtree to fxtree
			TreeItem<String> child = proofToFxTree(pRoot.child(i));
			
			// add subtree to root
			fxRoot.getChildren().add(child);
		}
		
		// return the fxroot
		return fxRoot;
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
