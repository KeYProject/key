// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.StringReader;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Stack;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.SwingWorker;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.init.DependencyContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.key.util.ProgressMonitor;


public final class ProblemLoader implements Runnable {

    private File file;
    private MainWindow main;    
    private KeYMediator mediator;

    private Proof proof = null;
    private Iterator<Node> children = null;

    private Node currNode = null;
    private KeYExceptionHandler exceptionHandler = null;
    private Goal currGoal = null;
    private String currTacletName = null;
    private int currFormula = 0;
    private PosInTerm currPosInTerm = PosInTerm.TOP_LEVEL;
    private Contract currContract = null;
    private Stack stack = new Stack();
    private LinkedList loadedInsts = null;
    private ImmutableList<IfFormulaInstantiation> ifFormulaList 
    	= ImmutableSLList.<IfFormulaInstantiation>nil();
    private ImmutableList<PosInOccurrence> builtinIfInsts;
    private int currIfInstFormula;
    private PosInTerm currIfInstPosInTerm;


    ProblemInitializer init;
    InitConfig iconfig;

    private SwingWorker worker;
    private ProgressMonitor pm;
    private ProverTaskListener ptl;
    
    public ProblemLoader(File file, MainWindow main) {
        this.main = main;
        this.mediator  = main.getMediator();        
        this.file = file;
        this.exceptionHandler = mediator.getExceptionHandler();

        addProgressMonitor(main.getUserInterface());
    }    
      
    public void addProgressMonitor(ProgressMonitor pm) {
        this.pm = pm;
    }

    public void addTaskListener(ProverTaskListener ptl) {
        this.ptl = ptl;
    }
    
    /** 
     * updates a possibly existing status line with the given information
     * @param status the String to be printed in the status line
     */
    public void setStatusLine(String status) {
        if (main != null) {
            main.setStatusLine(status);
        }
    }

    /**
     * updates a possibly existing status line with the given status information
     * and sets a maximum value for the progress bar
     * @param status the String with the status information
     * @param nr the int used a maximum value for a progress bar
     */
    public void setStatusLine(String status, int nr) {
        if (main != null) {
            main.setStatusLine(status, nr);
        }
    }
    
    /**
     * resets a possibly existing statusline to its standard text
     */
    public void setStandardStatusLine() {
        if (main != null) {
            main.setStandardStatusLine();
        }        
    }


    public void run() {
        /* Invoking start() on the SwingWorker causes a new Thread
         * to be created that will call construct(), and then
         * finished().  Note that finished() is called even if
         * the worker is interrupted because we catch the
         * InterruptedException in doWork().
         */
        worker = new SwingWorker() {
                private long time;
		public Object construct() {
                    time = System.currentTimeMillis();
                    Object res = doWork();
                    time = System.currentTimeMillis() - time;
		    return res;
		}
		public void finished() {
		    mediator.startInterface(true);
		    final String msg = (String) get();
		    if (ptl != null) {                        
                        final TaskFinishedInfo tfi = new DefaultTaskFinishedInfo(ProblemLoader.this, 
                                msg, proof, time, 
                                (proof != null ? proof.countNodes() : 0),                                
                                (proof != null ? proof.countBranches() -
                                        proof.openGoals().size() : 0));
                        ptl.taskFinished(tfi);
		    }
		}
        };
        mediator.stopInterface(true);
        if (ptl != null) ptl.taskStarted("Loading problem ...", 0);
        worker.start();
    }


    /**
     * @param file	the file or directory the user has chosen in the Open dialog
     * @return 		the corresponding input object for the selected file/directory
     * @throws FileNotFoundException 
     * @throws IllegalArgumentException if the user has selected a file with an unsupported extension
     *                          an exception is thrown to indicate this
     */
    public EnvInput createEnvInput(File file) 
    throws FileNotFoundException {                
        
        final String filename = file.getName();
        
        if (filename.endsWith(".java")){ 
            // java file, probably enriched by specifications
            if(file.getParentFile() == null) {
                return new SLEnvInput(".");
            } else {
                return new SLEnvInput(file.getParentFile().getAbsolutePath());
            }            
        } else if (filename.endsWith(".key") || 
                filename.endsWith(".proof")) {
            // KeY problem specification or saved proof
            return new KeYUserProblemFile(filename, file, pm);
            
        } else if (file.isDirectory()){ 
            // directory containing java sources, probably enriched 
            // by specifications
            return new SLEnvInput(file.getPath());
        } else {
            if (filename.lastIndexOf('.') != -1) {
                throw new IllegalArgumentException
                ("Unsupported file extension \'"+
                        filename.substring(filename.lastIndexOf('.'))+
                        "\' of read-in file " + filename +
                        ". Allowed extensions are: .key, .proof, .java or "+
                "complete directories."); 
            } else {
                throw new FileNotFoundException("File or directory\n\t "+
                        filename + "\n not found.");
            }
        }                
    }

   private Object doWork() {
       String status = "";
       EnvInput envInput = null;
       ProofOblInput po = null;
       try{
           try{
               envInput = createEnvInput(file);
               init = main.createProblemInitializer(); 
               InitConfig initConfig = init.prepare(envInput);

               final String chooseContract;
               if(envInput instanceof KeYFile) {
        	   chooseContract = ((KeYFile)envInput).chooseContract();
               } else {
        	   chooseContract = null;
               }
               if(envInput instanceof ProofOblInput && chooseContract == null) {
        	   po = (ProofOblInput) envInput;
               } else if(chooseContract != null 
        	         && chooseContract.length() > 0) {
        	   final Contract contract
        	   	= initConfig.getServices()
        	                    .getSpecificationRepository()
        	                    .getContractByName(chooseContract);
        	   if(contract == null) {
        	       throw new RuntimeException("Contract not found: " 
        		                          + chooseContract);
        	   } else {
                       po = contract.createProofObl(initConfig, contract);
                   }
        	   
               } else { 
        	   ProofManagementDialog.showInstance(initConfig);
        	   if(ProofManagementDialog.startedProof()) {
        	       return status;
        	   } else {
        	       return "Aborted.";
        	   }
               }

               init.startProver(initConfig, po);

               proof = mediator.getSelectedProof();
               mediator.stopInterface(true); // first stop (above) is not enough
               // as there is no problem at that time
               setStatusLine("Loading proof");
               currNode = proof.root(); // initialize loader
               children = currNode.childrenIterator(); // --"--
               iconfig = proof.env().getInitConfig();
               if(envInput instanceof KeYUserProblemFile) {
        	   init.tryReadProof(this, (KeYUserProblemFile)envInput);
               }
	       setStandardStatusLine();
           
	   } catch (ExceptionHandlerException e) {
//	       e.printStackTrace();
	       throw e;
	   } catch (Throwable thr) {
	       exceptionHandler.reportException(thr);
               status =  thr.getMessage();
               System.err.println("2");
	   }
       } catch (ExceptionHandlerException ex){
	       setStatusLine("Failed to load " 
		             + (envInput == null 
		        	 ? "problem/proof" : envInput.name()));
	       status =  ex.toString();
       }
       finally {
           mediator.resetNrGoalsClosedByHeuristics();
           if (po != null && po instanceof KeYUserProblemFile){
               ((KeYUserProblemFile) po).close();
           }
       }
       return status;
   }



    public void loadPreferences(String preferences) {
        final ProofSettings proofSettings = ProofSettings.DEFAULT_SETTINGS;
        proofSettings.loadSettingsFromString(preferences);
    }


    // note: Expressions without parameters only emit the endExpr signal
    public void beginExpr(char id, String s) {
        //System.out.println("start "+id+"="+s);
        
        //start no new commands until the ignored branch closes
        //count sub-branches though
        switch (id) {
        case 'b' :
            stack.push(children);
            if (children.hasNext()) currNode = children.next();
            break;
	case 'r' : 
            if (currNode == null) currNode = children.next();
            // otherwise we already fetched the node at branch point
            currGoal      = proof.getGoal(currNode);
            mediator.getSelectionModel().setSelectedGoal(currGoal);
            currTacletName= s;
            // set default state
            currFormula   = 0;
            currPosInTerm = PosInTerm.TOP_LEVEL;
            loadedInsts   = null;
            ifFormulaList = ImmutableSLList.<IfFormulaInstantiation>nil();
            break;

        case 'f' : //formula
            final int formula = Integer.parseInt(s);
            if(builtinIfInsts != null) {
        	currIfInstFormula = formula;
            } else {
        	currFormula = formula;
            }
            break;

        case 't' : //term
            final PosInTerm pos = PosInTerm.parseReverseString(s);
            if(builtinIfInsts != null) {
        	currIfInstPosInTerm = pos;
            } else {
        	currPosInTerm = pos;
            }
            break;

        case 'i' :
            if (loadedInsts == null) loadedInsts = new LinkedList();
            loadedInsts.add(s);
            break;
            
	case 'h' :
	    //             Debug.fail("Detected use of heuristics!");
	    break;
	case 'q' : // ifseqformula      
            Sequent seq = currGoal.sequent();
            ifFormulaList = ifFormulaList.append(
                    new IfFormulaInstSeq(seq, Integer.parseInt(s)));    
            break;
        case 'd' : // ifdirectformula      
            ifFormulaList = ifFormulaList.append(
                new IfFormulaInstDirect(
                    new SequentFormula(parseTerm(s, proof))));
            break;
        case 'u' : //UserLog
            if(proof.userLog==null)
                proof.userLog = new Vector<String>();
            proof.userLog.add(s);
            break;
        case 'v' : //Version log
            if(proof.keyVersionLog==null)
                proof.keyVersionLog = new Vector<String>();
            proof.keyVersionLog.add(s);
            break;
        case 's' : //ProofSettings
            //System.out.println("---------------\n" + s + "------------\n");
            //necessary for downward compatibility of the proof format
            loadPreferences(s);
            break;
        case 'n' : //BuiltIn rules
            if (currNode == null) currNode = children.next();
            currGoal      = proof.getGoal(currNode);
            mediator.getSelectionModel().setSelectedGoal(currGoal);
            currTacletName = s;
            // set default state
            currFormula   = 0;
            currPosInTerm = PosInTerm.TOP_LEVEL;
            builtinIfInsts = null;
            break;
        case 'c' : //contract
            currContract = proof.getServices().getSpecificationRepository().getContractByName(s);
            if(currContract == null) {
                throw new RuntimeException("Error loading proof: contract \"" + s + "\" not found.");
            }
            break;
        case 'x' : //ifInst (for built in rules)
            if(builtinIfInsts == null) {
        	builtinIfInsts = ImmutableSLList.<PosInOccurrence>nil();
            }
            currIfInstFormula = 0;
            currIfInstPosInTerm = PosInTerm.TOP_LEVEL;
            break;
        case 'w' : //newnames
            final String[] newNames = s.split(",");
            ImmutableList<Name> l = ImmutableSLList.<Name>nil();
            for (int in = 0; in < newNames.length; in++) {
                l = l.append(new Name(newNames[in]));
            }
            proof.getServices().getNameRecorder().setProposals(l);
            break;
        case 'e': //autoModeTime
            try {
                proof.addAutoModeTime(Long.parseLong(s));
            } catch (NumberFormatException e) {
                // ignore
            }
            break;
        }
    }


    public void endExpr(char id, int linenr) {
        //System.out.println("end "+id);
        //read no new commands until ignored branch closes
        switch (id) {
        case 'b' :
            children = (Iterator<Node>) stack.pop();           
            break;
        case 'a' :
            if (currNode != null) {
                currNode.getNodeInfo().setInteractiveRuleApplication(true);
            }
            break;
        case 'r' :
            try{
               currGoal.apply(constructApp());
               children = currNode.childrenIterator();
               currNode = null;
            } catch(Exception e) {
                throw new RuntimeException("Error loading proof. Line "+
                    linenr+" rule: "+currTacletName,e);
            }
            break;
        case 'n' :
            try {
                currGoal.apply(constructBuiltinApp());
                children = currNode.childrenIterator();
                currNode = null;
            } catch (BuiltInConstructionException e) {
                throw new RuntimeException("Error loading proof. Line "+
                    linenr+" rule: "+currTacletName,e);
            }
            break;
        case 'x' : //ifInst (for built in rules)
            try {
        	final PosInOccurrence ifInst 
        		= PosInOccurrence.findInSequent(currGoal.sequent(),
                                                    	currIfInstFormula,
                                                    	currIfInstPosInTerm);
        	builtinIfInsts = builtinIfInsts.append(ifInst);        	
            } catch(RuntimeException e) {
        	System.out.println("formula: " + currIfInstFormula);
        	System.out.println("term: " + currIfInstPosInTerm);
                throw new RuntimeException("Error loading proof. Line "+
                    linenr +" rule: "+currTacletName,e);
            }
            break;                        
        }

    }

    /**
     * Constructs rule application for UpdateSimplification from
     * current parser information
     *
     * @return current rule application for updateSimplification
     */
    private BuiltInRuleApp constructBuiltinApp()
                               throws BuiltInConstructionException {
        BuiltInRuleApp ourApp = null;
        //PosInSequent posInSeq = null;
        PosInOccurrence pos = null;

        if (currFormula != 0) { // otherwise we have no pos
            try {
        	pos = PosInOccurrence.findInSequent(currGoal.sequent(),
                                                    currFormula,
                                                    currPosInTerm);
            } catch(RuntimeException e) {
        	throw new BuiltInConstructionException(e);
            }
        }

        if (currContract != null) {
            ourApp = new ContractRuleApp(pos, currContract);
            currContract = null;
            if(builtinIfInsts != null) {
        	ourApp.setIfInsts(builtinIfInsts);
        	builtinIfInsts = null;
            }
            return ourApp;
        }

        final ImmutableSet<RuleApp> ruleApps =
            mediator.getBuiltInRuleApplications(currTacletName, pos);

        if (ruleApps.size() != 1) {
            if (ruleApps.size() < 1) {
                throw new BuiltInConstructionException
                (currTacletName +
                    " is missing. Most probably the binary "+
                    "for this built-in rule is not in your path or " +
                    "you do not have the permission to execute it.");
            } else {
                throw new BuiltInConstructionException
                (currTacletName + ": found " + ruleApps.size() +
                    " applications. Don't know what to do !\n" +
                    "@ " + pos);
            }
        }
        ourApp = (BuiltInRuleApp) ruleApps.iterator().next();
        builtinIfInsts = null;
        return ourApp;
    }

    private TacletApp constructApp() throws AppConstructionException {

        TacletApp ourApp = null;
        PosInOccurrence pos = null;

        Taclet t = iconfig.lookupActiveTaclet(new Name(currTacletName));
        if (t==null) {
            ourApp = currGoal.indexOfTaclets().lookup(currTacletName);
        } else {
            ourApp = NoPosTacletApp.createNoPosTacletApp(t);
        }
        Services services = mediator.getServices();
        

        if (currFormula != 0) { // otherwise we have no pos
            pos = PosInOccurrence.findInSequent(currGoal.sequent(),
                                                currFormula,
                                                currPosInTerm);
//System.err.print("Want to apply "+currTacletName+" at "+currGoal);
             //this is copied from TermTacletAppIndex :-/

            ourApp = ((NoPosTacletApp)ourApp).matchFind(pos, services);
            ourApp = ourApp.setPosInOccurrence(pos, services);
        }


        ourApp = constructInsts(ourApp, services);

        ourApp = ourApp.setIfFormulaInstantiations(ifFormulaList,
                                                   services);

        if (!ourApp.complete()) {
            ourApp = ourApp.tryToInstantiate(proof.getServices());
        }

        return ourApp;
    }



    /** 1st pass: only VariableSV */
    public static TacletApp parseSV1(TacletApp app, SchemaVariable sv,
                                     String value, Services services) {
        LogicVariable lv = new LogicVariable(new Name(value),
                                           app.getRealSort(sv, services));
        Term instance = TermFactory.DEFAULT.createTerm(lv);
        return app.addCheckedInstantiation(sv, instance, services,true);
    }


    /** 2nd pass: all other SV */
    public static TacletApp parseSV2(TacletApp app, 
	    			     SchemaVariable sv,
                                     String value, 
                                     Goal targetGoal) {        
        final Proof p = targetGoal.proof();
        final Services services = p.getServices();
        TacletApp result;
        if(sv instanceof VariableSV) {
            // ignore -- already done
            result = app;
        } else if(sv instanceof ProgramSV) {
	    final ProgramElement pe = 
	        TacletInstantiationsTableModel.getProgramElement(
		    app, value, sv, services);
	    result = app.addCheckedInstantiation(sv, pe, services, true);
        } else if(sv instanceof SkolemTermSV) {
	    result = app.createSkolemConstant ( value, sv, true, services );
        } else {
            Namespace varNS = p.getNamespaces().variables();
	    varNS = app.extendVarNamespaceForSV(varNS, sv);
	    Term instance = parseTerm(value, p, varNS, 
	            targetGoal.getVariableNamespace(varNS));
	    result = app.addCheckedInstantiation(sv, instance, services, true); 
        }
        return result;
    }


    private TacletApp constructInsts(TacletApp app, Services services) {
        if (loadedInsts == null) return app;
        ImmutableSet<SchemaVariable> uninsts = app.uninstantiatedVars();

        // first pass: add variables
        Iterator it = loadedInsts.iterator();
        while (it.hasNext()) {
            String s = (String) it.next();
            int eq = s.indexOf('=');
            String varname = s.substring(0, eq);
            String value = s.substring(eq+1, s.length());

            SchemaVariable sv = lookupName(uninsts, varname);
            if (sv==null) {
//                throw new IllegalStateException(
//                    varname+" from \n"+loadedInsts+"\n is not in\n"+uninsts);
                System.err.println(varname+" from "+app.rule().name()+" is not in uninsts");
                continue;
            }

            if (sv instanceof VariableSV) {
                app = parseSV1(app, sv, value, services);
            }
        }

        // second pass: add everything else
        uninsts = app.uninstantiatedVars();
        it = loadedInsts.iterator();
        while (it.hasNext()) {
            String s = (String) it.next();
            int eq = s.indexOf('=');
            String varname = s.substring(0, eq);
            String value = s.substring(eq + 1, s.length());
            SchemaVariable sv = lookupName(uninsts, varname);
            if(sv == null) {
        	continue;
            }
            app = parseSV2(app, sv, value, currGoal);
        }

        return app;
    }


    public static Term parseTerm(String value, Proof proof,
            Namespace varNS, Namespace progVar_ns) {
        try {
            return new DefaultTermParser().
                parse(new StringReader(value), null,
                      proof.getServices(),
                      varNS,
                      proof.getNamespaces().functions(),
                      proof.getNamespaces().sorts(),
                      progVar_ns,
                      new AbbrevMap());
        } catch(ParserException e) {
            throw new RuntimeException("Error while parsing value "+value+
                                       "\nVar namespace is: "+varNS+"\n", e);
        }
    }
    public static Term parseTerm(String value, Services services,
            Namespace varNS, Namespace progVar_ns) {
        try { 
            return new DefaultTermParser().
                parse(new StringReader(value), null,
                      services,
                      varNS,
                      services.getNamespaces().functions(),
                      services.getNamespaces().sorts(),
                      progVar_ns,
                      new AbbrevMap());
        } catch(ParserException e) {
            throw new RuntimeException("Error while parsing value "+value+
                                       "\nVar namespace is: "+varNS+"\n", e);
        }
    }

    public static Term parseTerm(String value, Proof proof) {
        return parseTerm(value, proof, proof.getNamespaces().variables(),
                proof.getNamespaces().programVariables());
    }


    private SchemaVariable lookupName(ImmutableSet<SchemaVariable> set, String name) {
        Iterator<SchemaVariable> it = set.iterator();
        while (it.hasNext()) {
            SchemaVariable v = it.next();
            if (v.name().toString().equals(name)) return v;
        }
        return null; // handle this better!
    }

    private static class AppConstructionException extends Exception {

        /**
         * 
         */
        private static final long serialVersionUID = -6534063595443883709L; }

    private static class BuiltInConstructionException extends Exception {
	/**
         * 
         */
        private static final long serialVersionUID = -735474220502290816L;
    BuiltInConstructionException(String s) {
	    super(s);
	}
	BuiltInConstructionException(Throwable cause) {
	    super(cause);
	}	
    }

    public KeYExceptionHandler getExceptionHandler() {
        return exceptionHandler;
    }
}
