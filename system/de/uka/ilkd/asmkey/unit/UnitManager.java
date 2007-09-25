// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.regex.Matcher;

import de.uka.ilkd.asmkey.gui.ProverFrame;
import de.uka.ilkd.asmkey.parser.ast.AstProof;
import de.uka.ilkd.asmkey.parser.tree.DeclarationParserFactory;
import de.uka.ilkd.asmkey.proof.AsmProof;
import de.uka.ilkd.asmkey.proof.AsmProofLoader;
import de.uka.ilkd.asmkey.proof.AsmProofSaver;
import de.uka.ilkd.asmkey.proof.decproc.AsmDecisionProcedureTranslationFactory;
import de.uka.ilkd.asmkey.proof.init.InitConfig;
import de.uka.ilkd.asmkey.rule.StepRule;
import de.uka.ilkd.asmkey.storage.StorageException;
import de.uka.ilkd.asmkey.storage.StorageManager;
import de.uka.ilkd.asmkey.unit.base.*;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProofSettings;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ldt.LDT;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.GlobalProofMgt;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleConfig;
import de.uka.ilkd.key.rule.ListOfBuiltInRule;
import de.uka.ilkd.key.rule.SLListOfBuiltInRule;
import de.uka.ilkd.key.rule.SimplifyIntegerRule;


/**
 * instances of this class are responsible for the
 * "logical" loading and saving of units and proofs
 * the actual handling of files is done by the storage
 * Manager, in particular, the UnitManager never has
 * to manipulate paths of files directly
 * the users organises its files as "projects". a unit manager
 * is responsible for a single project.
 * when the user changes the project, the base+user units are
 * reloaded.
 *
 * @see StorageManager
 * @author Stanislas Nanchen
 */
public class UnitManager {

    /* --- static final constants --- */

    public static final int NEW = 0;
    public static final int LOADING = 1;
    public static final int BASE_LOADED = 2;
    public static final int OPERATING = 3;
    public static final int STOPPED = 4;
    public static final int ERROR = -1;
    
    /**
     * the status of the manager: as the operation of the UnitManager is 
     * a complicated one, we introduce a status field that can take the following
     * values:
     * - NEW: the manager was just created and awaits order to load the units
     *        that will be given to him by his StorageManager.
     * - LOADING: the manager is currently loading the units and putting in place
     *            the UnitGraph and the UnitNamespaces;
     * - OPERATING: the manager has successfully loaded the units and is now 
     *              operating, serves as access point to get into the namespaces
     *              to obtain info about lemmas status, etc...
     * - ERROR: there was an error in the loading or in the operation and the manager
     *          should no more be used.
     */
    private int status;
    private StorageManager storage;
    private BaseUnitParser baseparser;
    private UnitParser parser;
    private UnitGraph graph;
    private ImportInfo[] baseInfos;
    private AbstractBaseUnit[] base;
    private String project;
    private KeYMediator mediator;
    private ProofSettings settings;
    private de.uka.ilkd.asmkey.logic.SimultaneousUpdateSimplifier simplifier;


    private static ListOfBuiltInRule DEFAULT_BUILT_IN_RULES;

    static {
	// step rule
	ListOfBuiltInRule list = SLListOfBuiltInRule.EMPTY_LIST.
	    prepend(new StepRule());//.prepend(new FunctionOperatorRule());
	// check whether "Simplify" is in $PATH. If not,  the 
	// taclet "Run Decision Procedure" won't be available.
	try {
	    
	    File file = File.createTempFile("key-simplify", null);
	    PrintWriter out = new PrintWriter(new FileWriter(file));
	    out.println("TRUE");
	    out.close();
	    Process p = Runtime.getRuntime().exec
		(new String[]{ "Simplify", file.getPath() });
	    list = list.prepend
		(new SimplifyIntegerRule(new AsmDecisionProcedureTranslationFactory()));
	    file.delete();
	}
	catch (IOException e){}
	finally {
	    DEFAULT_BUILT_IN_RULES = list;
	}
    }

    public UnitManager(StorageManager storage, UnitListener listener,
		       DeclarationParserFactory factory, String project,
		       KeYMediator mediator) { 
	resetBaseUnits();
	this.project = project;
	this.storage = storage;
	this.graph = new UnitGraph();
	this.status = UnitManager.NEW;
	this.baseparser = new BaseUnitParser(this, listener, this.graph, this.storage, factory);
	this.parser = new UnitParser(this, listener,
				     this.graph, this.storage, factory, this.project);
	this.baseInfos = new ImportInfo[0];
	this.mediator = mediator;
	this.settings = ProofSettings.DEFAULT_SETTINGS;
	this.simplifier = new de.uka.ilkd.asmkey.logic.SimultaneousUpdateSimplifier();
    }

    public UnitManager(StorageManager storage, UnitListener listener, String project,
		       KeYMediator mediator) { 
	this(storage, listener, DeclarationParserFactory.DEFAULT, project, mediator);
    }
	
    public int status() {
	return status;
    }

    public ImportInfo[] baseImportInfos() throws UnitException {
	checkBase();
	return baseInfos;
    }

    public AbstractBaseUnit[] base() throws UnitException {
	checkBase();
	return base;
    }

    private void checkBase() throws UnitException {
	if (status() < BASE_LOADED) {
	    throw new UnitException("The base has not been yet loaded.");
	}
    }
    
    /**
     * this method is the central method of the initialization phase of
     * the unit manager as it loads the base and the user files.
     */
    public void loadUnits() throws ParserException, UnitException {
	/* first we set the status */
	status = LOADING;
	
	try {
	    baseparser.parseUnits();
	    fillBaseUnitsCache();
	    status = BASE_LOADED;
	    parser.parseUnits();
	} catch (ParserException e) {
	    status = ERROR;
	    throw e;
	} catch (UnitException e) {
	    status = ERROR;
	    throw e;
	}
	
	/** we have finish the loading */
	status = OPERATING;
    }

    private void fillBaseUnitsCache() throws UnitException {
	IteratorOfUnit it = graph.orderedIterator();
	AbstractBaseUnit unit;
	int i;
	
	baseInfos = new ImportInfo[graph.size()];
	base = new AbstractBaseUnit[graph.size()];
	i = 0;
	while (it.hasNext()) {
	    try {
		unit = (AbstractBaseUnit) it.next();
	    } catch (ClassCastException e) {
		throw new UnitException("At this stage of loading, the graph should" +
					"contain only BaseUnits.");
	    }
	    base[i] = unit;
	    baseInfos[i++] = unit.standardImportInfo();
	}
    }

    private void resetBaseUnits() {
	Int.reset();
	Base.reset();
	Bool.reset();
	Sequence.reset();
    }

    /** thin method is used to get an ordered list
     * of the units in the current project
     * provisory
     */
    public Unit[] getOrderedUnits() throws UnitException {
	if (status() == UnitManager.OPERATING) {
	    Unit[] result = new Unit[graph().size()];
	    IteratorOfUnit it = graph().orderedIterator();
	    for(int i=result.length -1; i>=0; i--) {
		result[i] = it.next();
	    }
	    return result;
	} else {
	    throw new UnitException("The unit manager is not operating;" +
				    " impossible to retrieve the names of the units.");
	}
    }

    public UnitGraph graph() {
	return graph;
    }
    

    public static ListOfBuiltInRule builtInRules() {
	return DEFAULT_BUILT_IN_RULES;
    }

    /* --- problem + proof initialization done from UnitManager -- */


    //     //for tests only
    //     private ProblemInitializer(ProofOblInput problemFile)
    //                                                throws ProofInputException { 
    // 	this.problem=problemFile;
    // 	KeYFile ldtsForTests = new KeYFile("ldts",
    // 			RuleSource.initRuleFile("LDTsForTestsOnly.key"),
    // 			null);
    // 	settings = ProofSettings.THE_SETTINGS;
    // 	if (BASE_CONFIG==null) {
    // 	    initConfig = new InitConfig();
    // 	    initConfig.setNoStandardRules(false);
    // 	    initConfig.setBuiltInRules(DEFAULT_BUILT_IN_RULES);	
    //    	    BASE_CONFIG = initConfig;
    // 	    problem.setConfig(initConfig);
    // 	    readKeYFile(ldtsForTests);
    // 	}
    //     }
    
    //     //for tests only
    //     public static ProblemInitializer problemInitializerForTests(
    // 	                                 ProofOblInput problemFile)
    //                                             throws ProofInputException {
    // 	return new ProblemInitializer(problemFile);
    //     }
    
    //     public static String startProver(final ProofOblInput po) {
    // 	return startProver(po, null);
    //     }
    
    //     public static String startProver(final ProofOblInput po, 
    // 				     final ProofEnvironment env) {
    //         String startProverError = "";
    //         Main prover = Main.getInstance();
    //         prover.mediator().stopInterface(true);
    //         try{
    // 	    ProblemInitializer init =
    //                 new ProblemInitializer(ProofSettings.THE_SETTINGS, prover);
    // 	    prover.setStatusLine("Loading Problem");
    // 	    ProofAggregate pl;
    // 	    if (env!=null) {
    // 		pl = init.setUpProof(po, env);
    // 	    } else {
    // 		pl = init.setUpProof(po);
    // 	    }
    //         } catch (ProofInputException e) {
    //            prover.setStatusLine(po.name()+" failed");
    //            startProverError = e.toString();
    //         }
    // 	prover.setStandardStatusLine();
    //         prover.mediator().startInterface(true);
    // 	return startProverError;
    //     }
    
    private de.uka.ilkd.key.proof.init.InitConfig createInitConfig(Unit unit) {
	/* create environment with list of meta operators */
	/* the meta must be declared */
	/*Object[] metaOps = new Object[] {
	    join,
	    equiImp,
	    equiS,
	    big,
	    new MetaOpEqualArgs(),
	    new MetaDerived(),
	    new MetaAccTArgs(),
	    new MetaSCElimination(),
	    new MetaLogicalCondition(),
	    MetaOperator.META_ADD,
	    MetaOperator.META_SUB,
	    MetaOperator.META_MUL,
	    MetaOperator.META_DIV,
	    MetaOperator.META_MOD,
	    MetaOperator.META_LESS,
	    MetaOperator.META_GREATER,
	    MetaOperator.META_LEQ,
	    MetaOperator.META_GEQ,
	    MetaOperator.META_EQ,
	    };*/
	
	
	return null;
    }

    public ProofAggregate prepareProof(Name name, ProverFrame proverFrame) throws ProofInputException {
	Matcher m = UnitNamespace.unitPropMatcher(name);
	if (m.matches()) {
	    Unit unit = graph().get(new Name(m.group(1)));
	    AstProof astProof; 
	    try {
		astProof = storage.getAstProof(project, m.group(1), m.group(2));
	    } catch (StorageException e) {
		System.err.print("There is no proof for " + name + ": " + e.getMessage());
		astProof = null;
	    } catch (ParserException e) {
		throw new ProofInputException("The proof file for the prop " +
					      name + " contains syntax errors: " +
					      e.getMessage() + ", " + e.getLocation() +
					      ".");
	    }
	    Problem problem = unit.constructProblem(name);
	    ProofAggregate pl = setUpProof(problem);

	    proverFrame.addProblem(pl);
	    if (pl instanceof SingleProof && astProof != null) {
		// we reread the proof: until now, in ASMKEY, only 1 PO,
		// if necessary, store all the proofs with PO-names in 
		// the same file.
		try {
		    tryReadProof((AsmProof) pl.getFirstProof(), astProof);
		} catch (ClassCastException e) {
		    throw new ProofInputException("In AsmKeY, proofs objects must be AsmProof: " +
						  e.getMessage());
		}
	    }

	    return pl;
	} else {
	    throw new ProofInputException
		("Impossible to prepare the proof for prop/taclet " + name +
		 " : name not given in the format '[unit].[name]'.");
	}
    }
    
    /** determines an appropriate proof environment (creates one if
     * necessary) and sets up a proof in the environment. 
     */ 
    private ProofAggregate setUpProof(Problem problem) 
	throws ProofInputException {

	/* -- init config + proof environment for unit/problem  -- */
	/* TODO: init config once and for all for each unit ?? */

	InitConfig initConfig = new InitConfig(problem.unit());
	ProofEnvironment proofEnvironment = initConfig.getProofEnv();
	//initConfig.setBuiltInRules(DEFAULT_BUILT_IN_RULES);
	
	problem.setInitConfig(initConfig);
	problem.readActivatedChoices();

	proofEnvironment.setJavaModel(JavaModel.NO_MODEL);
	proofEnvironment.setRuleConfig(new RuleConfig
				       (initConfig.getActivatedChoices()));

	/* -- LDT bool + int -- */
	/* TO REVIEW */
	
	/* int integer LDT by hand. hack... is saved in settings in Choices no
	 * more in LDTSettings (this is strange....) */
	initConfig.initIntegerLDT();
	initConfig.initBooleanLDT();
	LDT[] ldts = initConfig.ldtModels();
	//TODO
	//mediator.getJavaInfo().getServices().getTypeConverter().init(ldts[1],
	//						     ldts[0]);

	/* -- registration of axioms and co -- */

	problem.unit().registerAllTaclets(proofEnvironment);
	proofEnvironment.registerRules(initConfig.builtInRules(), 
				       AxiomJustification.INSTANCE);
	GlobalProofMgt.getInstance().registerProofEnvironment
	    (proofEnvironment);

	/* -- proof obligations from problem -- */

	problem.setInitConfig(initConfig);
	ProofAggregate pl = problem.getPO();
	Proof[] proofs = pl.getProofs();
	NamespaceSet nss = initConfig.namespaces();
	for (int i=0; i < proofs.length; i++) {
	    proofs[i].setProofEnv(proofEnvironment);
	    proofs[i].setSimplifier(simplifier);
            proofs[i].setNamespaces(nss);
	}
	proofEnvironment.registerProof(problem, pl);

	/*ProcedurePool.put(mediator.getJavaInfo().getServices(),
	  initConfig.ruleNS());*/
	//GlobalProofMgt.getInstance().tryReuse(pl);	    

	return pl;
    }

    public void tryReadProof(AsmProof proof, AstProof astProof) throws ProofInputException {
	mediator.stopInterface(true);
	AsmProofLoader loader = new AsmProofLoader(proof, astProof);
	loader.loadProof();
	mediator.startInterface(false);
    }

    /* --- proof saving --- */

    public void saveProof(AsmProof proof) throws UnitException {
	try {
	    Matcher m = UnitNamespace.unitPropMatcher(proof.name());
	    if (m.matches()) {
		File file = storage.getProofFileForSaving(project, m.group(1),
							  m.group(2));
		AsmProofSaver saver = new AsmProofSaver(file, proof);
		saver.save();
	    } else {
		throw new UnitException
		    ("The proof name has not the format [Unit].[prop]");
	    }
	} catch (StorageException e) {
	    throw new UnitException(e);
	}
    }
 
}
