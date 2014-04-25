package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.InterruptListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SwingWorker3;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.gui.smt.ProofIndependentSMTSettings;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.smt.TGInfoDialog;
import de.uka.ilkd.key.gui.smt.TGOptionsDialog;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.util.Debug;
/**
 * Action which generates test cases for all open nodes. If the proof is closed,
 * test cases will be generated for nodes on which the emptyModality rule was applied. 
 * @author mihai
 *
 */
@SuppressWarnings("serial")
public class TestGenerationAction extends MainWindowAction {

	private static final String NAME = "T";
	private static final String TOOLTIP = "Generate test cases for open goals";
	private TGInfoDialog tgInfoDialog;
	
	public static Proof originalProof; 
	
	public TestGenerationAction(MainWindow mainWindow) {
		super(mainWindow);
		setName(NAME);
		setTooltip(TOOLTIP);
		init();
		
		
		
	}
	
	/** 
     * Registers the action at some listeners to update its status
     * in a correct fashion. This method has to be invoked after the
     * Main class has been initialised with the KeYMediator.
     */
    public void init() {
        final KeYSelectionListener selListener = new KeYSelectionListener() {

            public void selectedNodeChanged(KeYSelectionEvent e) {
                final Proof proof = getMediator().getSelectedProof();
                if (proof == null) {
                    // no proof loaded
                    setEnabled(false);
                } else {
                    setEnabled(true);
                }
            }
            
            public void selectedProofChanged(KeYSelectionEvent e) {
                selectedNodeChanged(e);
            }                
        };
        
        getMediator().addKeYSelectionListener(selListener);
        
        getMediator().addAutoModeListener(new AutoModeListener() {
            public void autoModeStarted(ProofEvent e) {
                getMediator().removeKeYSelectionListener(selListener);
                setEnabled(false);
            }

            public void autoModeStopped(ProofEvent e) {
                getMediator().addKeYSelectionListener(selListener);
                //selListener.selectedNodeChanged(null);
            }                
        });
        selListener.selectedNodeChanged(new KeYSelectionEvent(getMediator().getSelectionModel()));
    }
    
    /**
     * Creates a proof for each open node if the selected proof is open and a proof for each node
     * on which the emptyModality rules was applied if the selected proof is closed.
     * @param mediator
     * @param removeDuplicatePathConditions - if true no identical proofs will be created
     * @return
     */
    private Vector<Proof> createProofsForTesting(KeYMediator mediator, boolean removeDuplicatePathConditions){
    	Vector<Proof> res = new Vector<Proof>();
    	
		Proof oldProof = mediator.getSelectedProof();
		originalProof = oldProof;		
		
		List<Node> nodes = new LinkedList<Node>();
		ImmutableList<Goal> oldGoals = oldProof.openGoals();
		
		
		if(originalProof.closed()){
			getNodesWithEmptyModalities(originalProof.root(), nodes);
		}
		else{
			for(Goal goal : oldGoals){
				nodes.add(goal.node());
			}
		}
		
		
		Iterator<Node> oldGoalIter = nodes.iterator();
		
		while(oldGoalIter.hasNext()){
			try{
				Proof p=null;			
				if(removeDuplicatePathConditions)
					p = createProofForTesting_noDuplicate(oldGoalIter.next(),res);
				else
					p = createProofForTesting_noDuplicate(oldGoalIter.next(),null);
				
				if(p!=null)	res.add(p);
			}catch(Exception e){
				System.err.println(e.getMessage());
			}
		}
		
		return res;
    }
    /**
     * Adds all nodes on which the emptyModality rule was applied to the list.
     * @param root
     * @param nodes
     */
    private void getNodesWithEmptyModalities(Node root,List<Node> nodes){
    	if(root.getAppliedRuleApp()!=null){
    		RuleApp app = root.getAppliedRuleApp();
    		if(app.rule().name().toString().equals("emptyModality")){
    			nodes.add(root);
    		}
    	}
    	for(int i = 0; i < root.childrenCount(); ++i){
    		getNodesWithEmptyModalities(root.child(i), nodes);
    	}
    	
    }
    
    
    
    
    /**
     * Creates a proof with the specified node as its root. 
     * If an identical proof is found in otherProofs than null will be returned instead.
     * 
     * @param node
     * @param otherProofs
     * @return
     */
    private Proof createProofForTesting_noDuplicate(Node node, Vector<Proof> otherProofs){

    	//System.out.println("Create proof for test case from Node:"+node.serialNr());
    	
		Proof oldProof = node.proof();
		
		Sequent oldSequent = node.sequent();
		Sequent newSequent = Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,Semisequent.EMPTY_SEMISEQUENT);

		Iterator<SequentFormula> it = oldSequent.antecedent().iterator();
		while(it.hasNext()){
			SequentFormula sf = it.next();
			//Allow modailities in the antecedent
			//if(hasModalities(sf.formula())) continue;
			newSequent = newSequent.addFormula(sf, true, false).sequent();
		}
		it = oldSequent.succedent().iterator();
		while(it.hasNext()){
			SequentFormula sf = it.next();
			if(hasModalities(sf.formula())) continue;
			newSequent = newSequent.addFormula(sf, false, false).sequent();
		}
		
		//Check if a proof with the same sequent already exists.
		if(otherProofs!=null){
			for(Proof otherProof :otherProofs){
				if(otherProof.root().sequent().equals(newSequent)){
					//System.out.println("Found and skip duplicate proof for node:"+node.serialNr());
					return null;
				}
			}
		}
			
		Proof proof = new Proof("Test Case for NodeNr: "+ node.serialNr(), 
				newSequent, "", 
				oldProof.env().getInitConfig().createTacletIndex(), 
				oldProof.env().getInitConfig().createBuiltInRuleIndex(), 
				oldProof.getServices(), 
				oldProof.getSettings());
		
		proof.setProofEnv(oldProof.env());
		proof.setNamespaces(oldProof.getNamespaces());
		
		return proof;

	}
    
    private boolean hasModalities(Term t){
    	JavaBlock jb = t.javaBlock();
    	if(jb!=null && !jb.isEmpty()){
    		//System.out.println("Excluded javablock");
    		return true;
    	}
    	if(t.op()==UpdateApplication.UPDATE_APPLICATION){
    		//System.out.println("Exclude update application.");
    		return true;
    	}
    	boolean res = false;
    	for(int i=0; i<t.arity() && !res; i++){
    		res |= hasModalities(t.sub(i));
    	}
    	
    	return res;
    }
 
    
    @Override
	public void actionPerformed(ActionEvent e) {
    	TGOptionsDialog options = new TGOptionsDialog();
    	
    	
	    try{
	    	TGWorker worker = new TGWorker();
			worker.start();
	    }catch(Exception ie){
	    	tgInfoDialog.writeln("Test case generation stopped: "+ie.getMessage());
	    }
		
	}
	
	private class TGWorker extends SwingWorker3 implements InterruptListener{
		
		private boolean stop;
		
		private SolverLauncher launcher;
		

		
		private Vector<Proof> proofs;
		







		/**
		 * Removes all generated proofs.
		 */
		private void removeGeneratedProofs(){
			
			if(proofs == null){
				return;
			}
			
			for(Proof p : proofs){
				if(MainWindow.getInstance().getProofList().containsProof(p)){
					getMediator().getUI().removeProof(p);
					p.dispose();
				}
			}
			
			getMediator().setProof(originalProof);
			
			
		}
		
		
		
		

		

		@Override
		public void interruptionPerformed() {
			interrupt();
			tgInfoDialog.writeln("\nStopping test case generation.");
			stop = true;

			if(launcher != null){
				launcher.stop();
			}
			
			
			
			
			
		}
		
		/* 
	     * initiate the GUI stuff and relay to superclass
	     */
	    @Override 
	    public void start() {
	    	tgInfoDialog = new TGInfoDialog();
	        getMediator().stopInterface(true);
	        getMediator().setInteractive(false);
	        getMediator().addInterruptedListener(this);
	        super.start();
	    }

	    /* 
	     * finalise the GUI stuff
	     */
	    @Override 
	    public void finished() {
	    	removeGeneratedProofs();
	    	getMediator().setInteractive(true);
	    	getMediator().startInterface(true);
	    	getMediator().removeInterruptedListener(this);
	    	originalProof = null;
	    }

		@Override
		public Object construct() {
			
			
			if(!SolverType.Z3_CE_SOLVER.isInstalled(true)){
				tgInfoDialog.writeln("Could not find the z3 SMT solver. Aborting.");
				return null;
			}
			
			if(!SolverType.Z3_CE_SOLVER.isSupportedVersion()){
				tgInfoDialog.writeln("Warning: z3 supported versions are: "+Arrays.toString(SolverType.Z3_CE_SOLVER.getSupportedVersions()));
			}
			
			
			
			
			
			
			
			
			
			
			
			tgInfoDialog.writeln("Extracting test data constraints (path conditions).");
			proofs = createProofsForTesting(getMediator(),TGOptionsDialog.removeDuplicates());
			
			if(stop){
				
				return null;
			}
	    	
			if(proofs.size()>0)
				tgInfoDialog.writeln("Extracted "+proofs.size()+" test data constraints.");
			else
				tgInfoDialog.writeln("No test data constraints were extracted.");
			
			KeYMediator mediator = getMediator();
			Collection<SMTProblem> problems = new LinkedList<SMTProblem>();
			tgInfoDialog.writeln("Test data generation: appling semantic blasting macro on proofs");
			for(Proof proof : proofs){
				if(stop){					
					return null;
				}
				tgInfoDialog.write(".");
				ProofAggregate pa = new SingleProof(proof, "XXX");
	    		MainWindow mw = MainWindow.getInstance();
	    		mw.addProblem(pa);
				SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
								
				try {
					if(stop){					
						return null;
					}
					mediator.setProof(proof);
					macro.applyTo(mediator, null, null);
					problems.addAll(SMTProblem.createSMTProblems(mediator.getSelectedProof()));
					//mediator.getUI().removeProof(mediator.getSelectedProof());
				} catch (InterruptedException e) {
					Debug.out("Semantics blasting interrupted");
					tgInfoDialog.writeln("\n Warning: semantics blasting was interrupted. A test case will not be generated.");
				} catch(Exception e){
					tgInfoDialog.writeln(e.getLocalizedMessage());
					System.err.println(e);
				}
				
			}
			tgInfoDialog.writeln("\nDone applying semantic blasting.");
			
			mediator.setProof(originalProof);

			
			
			//getMediator().setInteractive(true);
	    	//getMediator().startInterface(true);
			
			
			Proof proof = mediator.getSelectedProof();
			
			//always use only 1 process when generating test cases
			ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().clone();
			piSettings.setMaxConcurrentProcesses(1);
			
			ProofDependentSMTSettings pdSettings = proof.getSettings().getSMTSettings().clone();
			pdSettings.invariantForall = true;
			
			
			//invoke z3 for counterexamples
            SMTSettings settings = new SMTSettings(pdSettings,piSettings,proof);
            
            
            
            launcher = new SolverLauncher(settings);
            launcher.addListener(tgInfoDialog);
           // launcher.addListener(new SolverListener(settings));
            
            
            List<SolverType> solvers = new LinkedList<SolverType>();
            solvers.add(SolverType.Z3_CE_SOLVER);  
            
            SolverType.Z3_CE_SOLVER.checkForSupport();
            
            
            
            if(stop){
				
				return null;
			}
            if(Thread.interrupted())return null;
            launcher.launch(solvers,
		            problems,
		            proof.getServices());		
			
			return null;
			
			
		}
		
	}
	
	
	
	

}
