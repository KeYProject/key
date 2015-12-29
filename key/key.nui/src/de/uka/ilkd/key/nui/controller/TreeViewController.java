package de.uka.ilkd.key.nui.controller;

import java.io.File;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.prooftree.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.fxml.FXML;
import javafx.scene.control.Label;
import javafx.scene.control.TreeView;

/**
 * controller for the treeView GUI element to visualize proofs
 */
public class TreeViewController {

    /**
     * The proofTree view on the GUI.
     */
    @FXML
    private TreeView<Label> proofTreeView;
    
	TreeConverter tConverter;

    /**
     * Initialization method for scene; loads the default proof
     */
    public void initialize() {
    	// The width and height of the icons used in the proofView
    	int iconSize = 15;
    	
    	// Create a new tree converter instance for conversion
    	// de.uka.ilkd.key.proof.Node --> de.uka.ilkd.key.nui.NUI.prooftree.NUINode 
    	// --> TreeItem<Label> (JavaFX)
    	tConverter = new TreeConverter(proofTreeView, iconSize);
    	
        // add CSS file to view
        String cssPath = this.getClass()
                .getResource("../components/treeView.css").toExternalForm();
        tConverter.addStylesheet(cssPath);
        
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
        tConverter.showTree();
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

        // convert proof tree to NUI Tree
        tConverter.convertProofToNUI(pRoot);
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
