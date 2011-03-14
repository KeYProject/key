// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.key.util.ProgressMonitor;


public final class ProblemLoader implements Runnable {

    private File file;
    private IMain main;    
    private KeYMediator mediator;

    private Proof proof = null;
    private Iterator<Node> children = null;

    private Node currNode = null;
    private KeYExceptionHandler exceptionHandler = null;
    private Goal currGoal = null;
    private String currTacletName = null;
    private int currFormula = 0;
    private PosInTerm currPosInTerm = PosInTerm.TOP_LEVEL;
    private OperationContract currContract = null;
    private Stack stack = new Stack();
    private LinkedList loadedInsts = null;
    private ImmutableList<IfFormulaInstantiation> ifFormulaList =
        ImmutableSLList.<IfFormulaInstantiation>nil();
    private Constraint matchConstraint = null;


    /* Proofs with meta variables have a special issue.
       When loading, rules are applied in an order different to the original
       one, sometimes yielding shorter proofs. The goal we are looking
       at might already have been closed. Then we need to ignore the
       rest of the current branch in the proof script.
    */
    private int ignoreBranchRest;


    ProblemInitializer init;
    InitConfig iconfig;

    private SwingWorker worker;
    private ProgressMonitor pm;
    private ProverTaskListener ptl;
    
    public ProblemLoader(File file, IMain main) {
        this.main = main;
        this.mediator  = main.mediator();        
        this.file = file;
        this.exceptionHandler = mediator.getExceptionHandler();

        addProgressMonitor(main.getProgressMonitor());
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
    protected EnvInput createEnvInput(File file) 
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
               init = new ProblemInitializer(main); 
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
        	   } else if(contract instanceof OperationContract) {
        	       po = new OperationContractPO(
        		       		initConfig, 
        		       		(OperationContract)contract);
        	   } else {
        	       po = new DependencyContractPO(
        		       		initConfig, 
        		       		(DependencyContract)contract);
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
               init.tryReadProof(this, po);
	       setStandardStatusLine();
           
	   } catch (ExceptionHandlerException e) {
	       throw e;
	   } catch (Throwable thr) {
	       exceptionHandler.reportException(thr);
               status =  thr.getMessage();
               System.out.println("2");
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
        if ((ignoreBranchRest > 0)&&(id!='b')) return; 
        switch (id) {
        case 'b' :
            stack.push(children);
            if (children.hasNext()) currNode = children.next();
            break;
	case 'r' : 
            if (currNode == null) currNode = children.next();
            // otherwise we already fetched the node at branch point
            currGoal      = proof.getGoal(currNode);
            // the goal may already have been closed due to the metavariable
            // issue described in the declaration of ignoreBranchRest
            if (currGoal==null) {
                ignoreBranchRest = stack.size();
                break;
            }
            mediator.getSelectionModel().setSelectedGoal(currGoal);
            currTacletName= s;
            // set default state
            currFormula   = 0;
            currPosInTerm = PosInTerm.TOP_LEVEL;
            loadedInsts   = null;
            ifFormulaList = ImmutableSLList.<IfFormulaInstantiation>nil();
            matchConstraint = Constraint.BOTTOM;
            break;

        case 'f' :
            currFormula   = Integer.parseInt(s);
            break;

        case 't' :
            currPosInTerm = PosInTerm.parseReverseString(s);
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
                    new ConstrainedFormula(parseTerm(s, proof))));
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
            break;
        case 'c' : //contract
            currContract = (OperationContract) proof.getServices().getSpecificationRepository().getContractByName(s);
            if(currContract == null) {
                throw new RuntimeException("Error loading proof: contract \"" + s + "\" not found.");
            }
            break;
        case 'o' : //userconstraint
            assert false : "metavariables are disabled";
            break;
        case 'm' : //matchconstraint
            final int index = s.indexOf('=');

            if (index < 0) {
                break;
            }

            final Term left = parseTerm(s.substring(0, index), proof);
            final Term right = parseTerm(s.substring(index + 1), proof);

            if (!(left.sort().extendsTrans(right.sort()) || right.sort()
                    .extendsTrans(left.sort()))) {
                break;
            }

            matchConstraint = matchConstraint.unify(left, right, null);
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
        if ((ignoreBranchRest > 0)&&(id!='b')) return; 
        switch (id) {
        case 'b' :
            children = (Iterator<Node>) stack.pop();
            // reached end of ignored branch?
            if (stack.size() < ignoreBranchRest) ignoreBranchRest = 0;
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

        final Constraint userConstraint = mediator.getUserConstraint()
                        .getConstraint();
        
        if (currContract!=null) {
            ourApp = new UseOperationContractRuleApp(pos, 
                                                     userConstraint, 
                                                     currContract);
            currContract=null;
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
        

        if (matchConstraint != Constraint.BOTTOM) {
            ourApp = ourApp.setMatchConditions(new MatchConditions(
        	    ourApp.instantiations(), 
        	    matchConstraint, 
        	    ourApp.newMetavariables(), 
        	    RenameTable.EMPTY_TABLE),
        	    services);
        }

        Constraint userC = mediator.getUserConstraint().getConstraint();

        if (currFormula != 0) { // otherwise we have no pos
            pos = PosInOccurrence.findInSequent(currGoal.sequent(),
                                                currFormula,
                                                currPosInTerm);
//System.err.print("Want to apply "+currTacletName+" at "+currGoal);
             //this is copied from TermTacletAppIndex :-/

            Constraint c = pos.constrainedFormula().constraint();
            if ( pos.termBelowMetavariable() != null ) {
                c = c.unify(
                   pos.constrainedFormula().formula().subAt(pos.posInTerm()),
                   pos.termBelowMetavariable(), mediator.getServices());
                if (!c.isSatisfiable()) return null;
            }
            ourApp = ((NoPosTacletApp)ourApp).matchFind(pos, c, services, userC);
            ourApp = ourApp.setPosInOccurrence(pos, services);
        }


        ourApp = constructInsts(ourApp, services);

        ourApp = ourApp.setIfFormulaInstantiations(ifFormulaList,
                                                   services, userC);

        if (!ourApp.sufficientlyComplete(services)) {
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

        AppConstructionException(String s) {
            super(s);
        }

        AppConstructionException(Throwable t) {
            super(t);
        }

        AppConstructionException(String s, Throwable t) {
            super(s, t);
        }

    }

    private static class BuiltInConstructionException extends Exception {
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

    private static class PairOfString {
        public String left;
        public String right;

        public PairOfString ( String p_left, String p_right ) {
            left  = p_left;
            right = p_right;
        }
    }
}
