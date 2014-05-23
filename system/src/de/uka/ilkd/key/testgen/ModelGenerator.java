package de.uka.ilkd.key.testgen;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.gui.smt.ProofIndependentSMTSettings;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.testgen.TestGenerationSettings;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.model.Model;

public class ModelGenerator implements SolverLauncherListener{
	
	private KeYMediator mediator;
	//the current term for which we look for models
	private Term term;
	//models that have been found until now
	private List<Model> models;
	//how many models we are looking for
	private int target;
	
	
	public ModelGenerator(Term t, int target, KeYMediator mediator) {
		this.mediator = mediator;
		this.term = t;
		this.target = target;
		models = new LinkedList<Model>();
	}

	
	/**
	 * Try finding a model for the term with z3.
	 */
	private void launch(){
		SolverLauncher launcher = prepareLauncher();
		SolverType solver = SolverType.Z3_CE_SOLVER;
		SMTProblem problem = new SMTProblem(term);
		launcher.addListener(this);
		launcher.launch(problem, mediator.getServices(), solver);		
	}
	/**
	 * Creates a SolverLauncher with the appropriate settings.
	 * @return
	 */
	private SolverLauncher prepareLauncher(){
		TestGenerationSettings settings = ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings();
		final ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE
		.getSMTSettings().clone();
		
		piSettings.setMaxConcurrentProcesses(settings.getNumberOfProcesses());
		final ProofDependentSMTSettings pdSettings = ProofDependentSMTSettings.getDefaultSettingsData();
		pdSettings.invariantForall = settings.invaraiantForAll();
		// invoke z3 for counterexamples
		final SMTSettings smtsettings = new SMTSettings(pdSettings,
				piSettings, null);		
		
		return new SolverLauncher(smtsettings);
	}

	@Override
    public void launcherStopped(SolverLauncher launcher,
            Collection<SMTSolver> finishedSolvers) {
		
		for(SMTSolver solver : finishedSolvers){
			
			SMTSolverResult result = solver.getFinalResult();
			if(result.equals(SMTSolverResult.ThreeValuedTruth.VALID) && models.size() < target){
				Model model = solver.getSocket().getQuery().getModel();
				models.add(model);
				addModelToTerm(model);
				launch();
			}
			else{
				finish();
			}			
		}	    
    }
	/**
	 * Changes the term such that when evaluated again with z3 another model will be generated.
	 * If we have a model (c1=v1 & c2 = v2 & ...) where c1, c2, ... are integer constants we change the term t to the following form:
	 * t & !(c1=v1 & c2 = v2 & ...)
	 * 
	 * @param m
	 */
	private void addModelToTerm(Model m){
		Sort intSort = mediator.getServices().getTypeConverter().getIntegerLDT().targetSort();
		TermBuilder tb = mediator.getServices().getTermBuilder();
		Namespace functions = mediator.getServices().getNamespaces().functions();
		Term tmodel=tb.tt();
		for(String c : m.getConstants().keySet()){
			
			Sort sort = m.getTypes().getOriginalConstantType(c);
			if(sort.equals(intSort)){
				String val = m.getConstants().get(c);
				int value = Integer.parseInt(val);							
				Function f = (Function) functions.lookup(c);				
				Term termConst =  tb.func(f);
				Term termVal = tb.zTerm(value);
				Term termEquals = tb.equals(termConst, termVal);
				tmodel = tb.and(tmodel,termEquals);			
			}			
		}
		if(!tmodel.equals(tb.tt())){
			Term notTerm = tb.not(tmodel);
			term = tb.add(term, notTerm);
		}
	}
	
	private void finish(){
		
	}

	@Override
    public void launcherStarted(Collection<SMTProblem> problems,
            Collection<SolverType> solverTypes, SolverLauncher launcher) {
	    
	    
    }
}
