package de.uka.ilkd.key.testgen;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.gui.smt.ProofIndependentSMTSettings;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.testgen.TestGenerationSettings;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.smt.SMTObjTranslator;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.lang.SMTSort;
import de.uka.ilkd.key.smt.model.Model;

public class ModelGenerator implements SolverLauncherListener{

	private KeYMediator mediator;
	private Sequent seq;


	//models that have been found until now
	private List<Model> models;
	//how many models we are looking for
	private int target;


	public ModelGenerator(Sequent s, int target, KeYMediator mediator) {
		this.mediator = mediator;
		this.seq = s;	

		this.target = target;
		models = new LinkedList<Model>();
	}


	/**
	 * Try finding a model for the term with z3.
	 */
	public void launch(){
		System.out.println("Launch");
		SolverLauncher launcher = prepareLauncher();
		SolverType solver = SolverType.Z3_CE_SOLVER;
		SMTProblem problem = new SMTProblem(sequentToTerm(seq));
		launcher.addListener(this);
		launcher.launch(problem, mediator.getServices(), solver);		
	}
	/**
	 * Creates a SolverLauncher with the appropriate settings.
	 * @return
	 */
	private SolverLauncher prepareLauncher(){
		TestGenerationSettings settings = ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings();
		final ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().clone();
		

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
	 * @param m the model
	 * @return true if the term has been changed
	 */
	private boolean addModelToTerm(Model m){
		//System.out.println("Model to term");

		TermBuilder tb = mediator.getServices().getTermBuilder();
		Namespace variables = mediator.getServices().getNamespaces().programVariables();
		Term tmodel=tb.tt();
		for(String c : m.getConstants().keySet()){

			SMTSort sort = m.getTypes().getTypeForConstant(c);

			if(sort!=null && sort.getId().equals(SMTObjTranslator.BINT_SORT)){
				//System.out.println("const: "+c);
				String val = m.getConstants().get(c);
				//System.out.println(val);
				int value = Integer.parseInt(val);
				ProgramVariable v = (ProgramVariable)variables.lookup(c);				
				Term termConst = tb.var(v);
				//Term termConst =  tb.func(f);
				Term termVal = tb.zTerm(value);
				Term termEquals = tb.equals(termConst, termVal);
				tmodel = tb.and(tmodel,termEquals);
			}
		}


		if(!tmodel.equals(tb.tt())){
			System.out.println(tmodel);
			Term notTerm = tb.not(tmodel);
			SequentFormula sf = new SequentFormula(notTerm);			
			Semisequent antecedent = seq.antecedent().insertFirst(sf).semisequent();
			seq = Sequent.createSequent(antecedent, seq.succedent());			
			return true;
		}
		return false;

	}

	private void finish(){
		System.out.println("\n\nFinished:\n");
		for(Model m :  models){
			System.out.println(m.toString());
		}
	}

	@Override
	public void launcherStarted(Collection<SMTProblem> problems,
			Collection<SolverType> solverTypes, SolverLauncher launcher) {
		System.out.println("\nStarted: ");
		for(SMTProblem p : problems){
			System.out.println(p.getTerm());
		}

	}

	public Term sequentToTerm(Sequent s) {

		ImmutableList<Term> ante = ImmutableSLList.nil();

		final TermBuilder tb = mediator.getServices().getTermBuilder();
		ante = ante.append(tb.tt());
		for (SequentFormula f : s.antecedent()) {
			ante = ante.append(f.formula());
		}

		ImmutableList<Term> succ = ImmutableSLList.nil();
		succ = succ.append(tb.ff());
		for (SequentFormula f : s.succedent()) {
			succ = succ.append(f.formula());
		}

		return tb.imp(tb.and(ante), tb.or(succ));

	}

}
