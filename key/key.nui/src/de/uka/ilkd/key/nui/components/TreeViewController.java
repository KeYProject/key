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
 *
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
	
//	private Proof getDefaultProof() {
//	    Proof p;
//	    Node n1;
//	    Node n2;
//	    Node n3;
//	    Node n4;
//	    Node n5;
//	    Node n6;
//	    Node n7;
//	    
//	    Sort s = new SortImpl(new Name("s"));
//		LogicVariable b1=new LogicVariable(new Name("b1"),s);
//		LogicVariable b2=new LogicVariable(new Name("b2"),s);
//		LogicVariable b3=new LogicVariable(new Name("b3"),s);
//		LogicVariable b4=new LogicVariable(new Name("b4"),s);
//		LogicVariable b5=new LogicVariable(new Name("b5"),s);
//		LogicVariable b6=new LogicVariable(new Name("b6"),s);
//		LogicVariable b7=new LogicVariable(new Name("b7"),s);
//
//		TermFactory tf = TacletForTests.services().getTermFactory();
//		
//		Term t_b1=tf.createTerm(Equality.EQUALS,
//			                tf.createTerm(b1),
//			                tf.createTerm(b1));
//		Term t_b2=tf.createTerm(Equality.EQUALS,
//			                tf.createTerm(b2),
//			                tf.createTerm(b2));
//		Term t_b3=tf.createTerm(Equality.EQUALS,
//			                tf.createTerm(b3),
//			                tf.createTerm(b3));
//		Term t_b4=tf.createTerm(Equality.EQUALS,
//			                tf.createTerm(b4),
//			                tf.createTerm(b4));
//		Term t_b5=tf.createTerm(Equality.EQUALS,
//			                tf.createTerm(b5),
//			                tf.createTerm(b5));
//		Term t_b6=tf.createTerm(Equality.EQUALS,
//			                tf.createTerm(b6),
//			                tf.createTerm(b6));
//		Term t_b7=tf.createTerm(Equality.EQUALS,
//			                tf.createTerm(b7),
//			                tf.createTerm(b7));
//
//		Sequent s1=Sequent.createSequent
//		    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
//		    SequentFormula(t_b1)).semisequent(),
//		     Semisequent.EMPTY_SEMISEQUENT); 
//		Sequent s2=Sequent.createSequent
//		    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
//			SequentFormula(t_b2)).semisequent(),
//		     Semisequent.EMPTY_SEMISEQUENT); 
//		Sequent s3=Sequent.createSequent
//		    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
//			SequentFormula(t_b3)).semisequent(),
//		     Semisequent.EMPTY_SEMISEQUENT); 
//		Sequent s4=Sequent.createSequent
//		    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
//			SequentFormula(t_b4)).semisequent(),
//		     Semisequent.EMPTY_SEMISEQUENT); 
//		Sequent s5=Sequent.createSequent
//		    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
//			SequentFormula(t_b5)).semisequent(),
//		     Semisequent.EMPTY_SEMISEQUENT); 
//		Sequent s6=Sequent.createSequent
//		    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
//			SequentFormula(t_b6)).semisequent(),
//		     Semisequent.EMPTY_SEMISEQUENT); 
//		Sequent s7=Sequent.createSequent
//		    (Semisequent.EMPTY_SEMISEQUENT.insert(0, new
//			SequentFormula(t_b7)).semisequent(),
//		     Semisequent.EMPTY_SEMISEQUENT); 
//
//		p=new Proof("TestProofTree", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
//
//		n1=new Node(p, s1);
//		n2=new Node(p, s2);
//		n3=new Node(p, s3);
//		n4=new Node(p, s4);
//		n5=new Node(p, s5);
//		n6=new Node(p, s6);
//		n7=new Node(p, s7);
//
//		n1.add(n2);
//		n1.add(n3);
//		n1.add(n4);
//		n3.add(n5);
//		n5.add(n6);
//		n5.add(n7);
//
//		p.setRoot(n1);
//	    
//	    return p;
//	}
	
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
