package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
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
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.util.Debug;

@SuppressWarnings("serial")
public class CounterExampleAction extends MainWindowAction {

	private static final String NAME = "CE";
	private static final String TOOLTIP = "Search for a counterexample for the selected goal";
	
	public static Proof originalProof; 
	
	public CounterExampleAction(MainWindow mainWindow) {
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
                    final Goal selGoal = getMediator().getSelectedGoal();
                    final Node selNode = getMediator().getSelectedNode();
                    //Can be applied only to root nodes
                    setEnabled(selNode.childrenCount()==0);
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
                selListener.selectedNodeChanged(null);
            }                
        });
        selListener.selectedNodeChanged(new KeYSelectionEvent(getMediator().getSelectionModel()));
    }
    
    private Proof createProof(KeYMediator mediator){

		Goal goal = mediator.getSelectedGoal();
		
		Node node = goal.node();
		Proof oldProof = node.proof();
		
		//originalProof = oldProof;
		
		Sequent oldSequent = node.sequent();
		Sequent newSequent = Sequent.createSequent(oldSequent.antecedent(), oldSequent.succedent());
		Proof proof = new Proof("Semantics Blasting: "+oldProof.name(), 
				newSequent, "", 
				oldProof.env().getInitConfig().createTacletIndex(), 
				oldProof.env().getInitConfig().createBuiltInRuleIndex(), 
				oldProof.getServices(), 
				oldProof.getSettings());
		
		proof.setProofEnv(oldProof.env());
		proof.setNamespaces(oldProof.getNamespaces());

		ProofAggregate pa = new SingleProof(proof, "XXX");
		
		MainWindow mw = MainWindow.getInstance();
		mw.addProblem(pa);
		
		mediator.goalChosen(proof.getGoal(proof.root()));		
		
		return proof;

	}
    
    private Vector<Proof> createProofsForTesting(KeYMediator mediator){
    	Vector<Proof> res = new Vector();
    	
		Proof oldProof = mediator.getSelectedGoal().proof();
		originalProof = oldProof;		
		
		
		ImmutableList<Goal> oldGoals = oldProof.openGoals();
		Iterator<Goal> oldGoalIter = oldGoals.iterator();
		
		while(oldGoalIter.hasNext()){
			res.add(createProofForTesting(oldGoalIter.next().node()));
		}
		
		return res;
    }

    private Proof createProofForTesting(Node node){

    	System.out.println("Create proof for test case from Node:"+node.serialNr());
    	
		Proof oldProof = node.proof();
		
		Sequent oldSequent = node.sequent();
		Sequent newSequent = Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,Semisequent.EMPTY_SEMISEQUENT);

		Iterator<SequentFormula> it = oldSequent.antecedent().iterator();
		while(it.hasNext()){
			SequentFormula sf = it.next();
			if(hasModalities(sf.formula())) continue;
			newSequent = newSequent.addFormula(sf, true, false).sequent();
		}
		it = oldSequent.succedent().iterator();
		while(it.hasNext()){
			SequentFormula sf = it.next();
			if(hasModalities(sf.formula())) continue;
			newSequent = newSequent.addFormula(sf, false, false).sequent();
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
    		System.out.println("Excluded javablock");
    		return true;
    	}
    	if(t.op()==UpdateApplication.UPDATE_APPLICATION){
    		System.out.println("Exclude update application.");
    		return true;
    	}
    	boolean res = false;
    	for(int i=0; i<t.arity() && !res; i++){
    		res |= hasModalities(t.sub(i));
    	}
    	
    	return res;
    }
    
/*
    private Proof createProofForTesting(KeYMediator mediator){

		Node node = mediator.getSelectedNode();
		Proof oldProof = node.proof();
		
		originalProof = oldProof;		
		
		Sequent oldSequent = node.sequent();
		Sequent newSequent = Sequent.createSequent(oldSequent.antecedent(), oldSequent.succedent());
		Proof proof = new Proof("Semantics Blasting: "+oldProof.name(), 
				newSequent, "", 
				oldProof.env().getInitConfig().createTacletIndex(), 
				oldProof.env().getInitConfig().createBuiltInRuleIndex(), 
				oldProof.getServices(), 
				oldProof.getSettings());
		
		proof.setProofEnv(oldProof.env());
		proof.setNamespaces(oldProof.getNamespaces());

		Goal newGoal = proof.openGoals().iterator().next();

		ImmutableList<Goal> oldGoals = oldProof.openGoals();
		int goalCount = oldGoals.size();
		
		System.out.println("Splitting goal in subgoals:"+goalCount);
		
		final ImmutableList<Goal> newSubGoals = newGoal.split(goalCount);
		
		TermBuilder termBuilder = oldProof.getServices().getTermBuilder();
		Term tt = termBuilder.tt();
		SequentFormula sf = new SequentFormula(tt);
		
		Iterator<Goal> newGoalIter = newSubGoals.iterator();
		Iterator<Goal> oldGoalIter = oldGoals.iterator();
		int counter = 0;
		
		while(oldGoalIter.hasNext() && newGoalIter.hasNext()){
			Goal newSubGoal = newGoalIter.next();
			Goal oldSubGoal = oldGoalIter.next();
			System.out.println("Initializing subgoal:"+counter);
			newSubGoal.setBranchLabel("Test Case "+counter++);
			Semisequent oldSemiSeq = oldSubGoal.node().sequent().succedent();
			SequentFormula oldSF = oldSemiSeq.get(oldSemiSeq.size()-1);
			newSubGoal.addFormula(new SequentFormula(oldSF.formula()), 
	                true, 
	                false);
		}
		
		ProofAggregate pa = new SingleProof(proof, "XXX");
		
		MainWindow mw = MainWindow.getInstance();
		mw.addProblem(pa);
		
		//mediator.goalChosen(proof.getGoal(proof.root()));		
		
		return proof;

	}
*/
    
    @Override
	public void actionPerformed(ActionEvent e) {
		//createProofForTesting(getMediator());
		Goal goal = getMediator().getSelectedGoal();		
		originalProof = goal.node().proof();

		Vector<Proof> proofs = createProofsForTesting(getMediator());

    	//The following loop is meant for debugging only and should be removed
    	for(Proof p:proofs){
    		ProofAggregate pa = new SingleProof(p, "XXX");
    		MainWindow mw = MainWindow.getInstance();
    		mw.addProblem(pa);
    	}
    	
		getMediator().setProof(originalProof);
		createProof(getMediator());	
		
		CEWorker worker = new CEWorker();
		worker.start();
	}
	
	private class CEWorker extends SwingWorker3 implements InterruptListener{

		@Override
		public void interruptionPerformed() {
			interrupt();
			
		}
		
		/* 
	     * initiate the GUI stuff and relay to superclass
	     */
	    @Override 
	    public void start() {
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
	    	getMediator().setInteractive(true);
	    	getMediator().startInterface(true);
	    	getMediator().removeInterruptedListener(this);
	    	originalProof = null;
	    }

		@Override
		public Object construct() {
			
			KeYMediator mediator = getMediator();
			Proof proof = mediator.getSelectedProof();
			SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
			
			try {
				macro.applyTo(mediator, null, null);
			} catch (InterruptedException e) {
				Debug.out("Semantics blasting interrupted");
			}
			
			getMediator().setInteractive(true);
	    	getMediator().startInterface(true);
			
			
			//invoke z3 for counterexamples
            SMTSettings settings = new SMTSettings(proof.getSettings().getSMTSettings(),
                            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),proof);
            SolverLauncher launcher = new SolverLauncher(settings);
            launcher.addListener(new SolverListener(settings));
            
            
            List<SolverType> solvers = new LinkedList<SolverType>();
            solvers.add(SolverType.Z3_CE_SOLVER);
            
            
            launcher.launch(solvers,
		            SMTProblem.createSMTProblems(proof),
		            proof.getServices());		
			
			return null;
			
			
		}
		
	}
	
	
	
	

}
