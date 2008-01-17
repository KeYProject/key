// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.StringReader;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Stack;
import java.util.Vector;

import de.uka.ilkd.hoare.init.HoareProfile;
import de.uka.ilkd.hoare.rule.HoareLoopInvRuleApp;
import de.uka.ilkd.hoare.rule.HoareLoopInvariantRule;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.SwingWorker;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.parser.*;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.PresentationFeatures;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAuflia;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.mgt.OldOperationContract;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;

public class ProblemLoader implements Runnable {

    File file;
    Main main;
    KeYMediator mediator;

    Proof proof = null;
    IteratorOfNode children = null;

    Node currNode = null;
    KeYExceptionHandler exceptionHandler = null;
    Goal currGoal = null;
    String currTacletName = null;
    int currFormula = 0;
    
    // got Hoare Loop Rule Loading; OLD
    private String hoareLoopInv;     
    
    PosInTerm currPosInTerm = PosInTerm.TOP_LEVEL;
    OldOperationContract currContract = null;
    Stack stack = new Stack();
    LinkedList loadedInsts = null;
    ListOfIfFormulaInstantiation ifSeqFormulaList =
        SLListOfIfFormulaInstantiation.EMPTY_LIST;


    ProblemInitializer init;
    InitConfig iconfig;

    /** if set uses the current problem instance instead of a new one */
    boolean keepProblem;

    /** the profile to be used */
    private Profile profile;
    
    private SwingWorker worker;
    
    public ProblemLoader(File file, Main main, Profile profile) {
        this(file, main, profile, false);
    }

    public ProblemLoader(File file, Main main, Profile profile, boolean keepProblem) {
        this.main = main;
        mediator  = main.mediator();
        this.file = file;
        this.profile = profile;
        this.exceptionHandler = mediator.getExceptionHandler();
        this.keepProblem = keepProblem;
    }


    public void run() {
        /* Invoking start() on the SwingWorker causes a new Thread
         * to be created that will call construct(), and then
         * finished().  Note that finished() is called even if
         * the worker is interrupted because we catch the
         * InterruptedException in doWork().
         */
        worker = new SwingWorker() {
		public Object construct() {
		    Object res = doWork();
		    return res;
		}
		public void finished() {
		    mediator.startInterface(true);
		    String msg = (String) get();
		    if(!"".equals(msg)) {
		        if(Main.batchMode){
			    System.exit(-1);
			} else {
			    new ExceptionDialog
				(mediator.mainFrame(), 
                                        exceptionHandler.getExceptions());
			    exceptionHandler.clear();
			}
		    } else {
			PresentationFeatures.
			    initialize(mediator.func_ns(), 
				       mediator.getNotationInfo(),
				       mediator.getSelectedProof());
		    }
		    if (Main.batchMode) {
			//System.out.println("Proof: " +proof.openGoals());
			if(proof.openGoals().size()==0) {
			    System.out.println("proof.openGoals.size=" + 
                                    proof.openGoals().size());
			    System.exit(0);
			}
		        mediator.startAutoMode();
		    }		   
		}
	    };
        mediator.stopInterface(true);
        worker.start();
    }


    /**
     * @param file	the file or directory the user has chosen in the Open dialog
     * @return 		the corresponding input object for the selected file/directory
     * @throws FileNotFoundException 
     * @throws IllegalArgumentException if the user has selected a file with an unsupported extension
     *                          an exception is thrown to indicate this
     */
    protected KeYUserProblemFile createProblemFile(File file) 
    throws FileNotFoundException {                
        
        final String filename = file.getName();
        
        if (filename.endsWith(".java")){ 
            // java file, probably enriched by JML specifications
            return new KeYJMLInput(filename, file, 
                    profile instanceof JavaTestGenerationProfile,
                    main.getProgressMonitor());
            
        } else if (filename.endsWith(".key") || 
                filename.endsWith(".proof")) {
            if (profile instanceof HoareProfile) {
                return new HoareUserProblemFile(filename, file,
                        main.getProgressMonitor(), Main.jmlSpecs);
            } else {
                // KeY problem specification or saved proof
                return new KeYUserProblemFile(filename, file, 
                        main.getProgressMonitor(), Main.jmlSpecs);
            }            
        } else if (file.isDirectory()){ 
            // directory containing JML-enriched java sources
            // prompt the 
            return new JavaInputWithJMLSpecBrowser(file.getPath(), file, 
                    profile instanceof JavaTestGenerationProfile, 
                    main.getProgressMonitor());            
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
       KeYUserProblemFile problemFile = null;
       try{
           try{
               if (!keepProblem) {
                   problemFile = createProblemFile(file);                  
	           init = new ProblemInitializer(main);            
                   init.startProver(problemFile, problemFile);
               }
               proof = mediator.getSelectedProof();
               mediator.stopInterface(true); // first stop (above) is not enough
               // as there is no problem at that time
               main.setStatusLine("Loading proof");
               currNode = proof.root(); // initialize loader
               children = currNode.childrenIterator(); // --"--
               iconfig = proof.env().getInitConfig();
               if (!keepProblem) {
                   init.tryReadProof(this, problemFile);
               } else {
                   main.setStatusLine("Loading proof", (int)file.length());
                   CountingBufferedInputStream cinp =
                       new CountingBufferedInputStream(
                           new FileInputStream(file),
                           main.getProgressMonitor(),
                           (int)file.length()/100);
                   KeYLexer lexer = new KeYLexer(cinp,
                       proof.getServices().getExceptionHandler());
                   KeYParser parser = new KeYParser(ParserMode.PROBLEM, lexer, 
                                                    proof.getServices());
                   antlr.Token t;
                   do { t = lexer.getSelector().nextToken();
                   } while (t.getType() != KeYLexer.PROOF);
                   parser.proofBody(this);
               }
	       main.setStandardStatusLine();
           
           // Inform the decproc classes that a new problem has been loaded
           // This is done here because all benchmarks resulting from one loaded problem should be
           // stored in the same directory
           DecisionProcedureSmtAuflia.fireNewProblemLoaded( file, proof );
           
	   } catch (ExceptionHandlerException e) {
	       throw e;
	   } catch (Throwable thr) {
	       exceptionHandler.reportException(thr);
               status =  thr.getMessage();
	   }
       } catch (ExceptionHandlerException ex){
	       main.setStatusLine("Failed to load problem/proof");
	       status =  ex.toString();
       }
       finally {
           if (problemFile != null && problemFile instanceof KeYUserProblemFile){
               ((KeYUserProblemFile) problemFile).close();
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
            ifSeqFormulaList = SLListOfIfFormulaInstantiation.EMPTY_LIST;
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
            ifSeqFormulaList = ifSeqFormulaList.append(
                new IfFormulaInstSeq(seq, Integer.parseInt(s)));
            break;
        case 'u' : //UserLog
            if(proof.userLog==null)
                proof.userLog = new Vector();
            proof.userLog.add(s);
            break;
        case 'v' : //Version log
            if(proof.keyVersionLog==null)
                proof.keyVersionLog = new Vector();
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
            loadedInsts = null;
            // set default state
            currFormula   = 0;
            currPosInTerm = PosInTerm.TOP_LEVEL;
            break;
        case 'c' : //contract
            currContract = (OldOperationContract) proof.getServices()
                             .getSpecificationRepository().getContractByName(s);
            break;             
        case 'z': // old save mode only for compatibility
            hoareLoopInv = s;
            break;
        }
    }


    public void endExpr(char id, int linenr) {
        //System.out.println("end "+id);
        switch (id) {
        case 'b' :
            children = (IteratorOfNode) stack.pop();
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
            pos = PosInOccurrence.findInSequent(currGoal.sequent(),
                                                currFormula,
                                                currPosInTerm);
        } else {
        }

        final Constraint userConstraint = mediator.getUserConstraint()
                        .getConstraint();
        
        if (currContract!=null) {
            ourApp = new MethodContractRuleApp(UseMethodContractRule.INSTANCE,
                    pos, userConstraint, currContract);
            currContract=null;
            return ourApp;
        }

        // old loading code
        if (hoareLoopInv != null) {
            Namespace varNS = currGoal.proof().getNamespaces().variables();
            
            final Term inv = 
                parseTerm(hoareLoopInv, proof, varNS, currGoal.createGlobalProgVarNamespace());
            
            ourApp = 
                new HoareLoopInvRuleApp(inv,  
                        HoareLoopInvariantRule.INSTANCE, pos, userConstraint);
            hoareLoopInv = null;
            return ourApp;
        }
        
        if ("Loop Invariant".equals(currTacletName)) {
            Namespace varNS = currGoal.proof().getNamespaces().variables();
            
            String str = (String) loadedInsts.removeFirst();
            final Term inv = parseTerm(str, proof, varNS, currGoal.createGlobalProgVarNamespace());                

            Term decreases = null;
            Name atPreDecFunc = null;
            if (loadedInsts.size()>0) {
                str = (String) loadedInsts.removeFirst();
                decreases = 
                    parseTerm(str, proof, varNS, currGoal.createGlobalProgVarNamespace());                
                
                str = (String) loadedInsts.removeFirst();
                atPreDecFunc = new Name(str);                                
            }            
            ourApp = 
                new HoareLoopInvRuleApp(inv, decreases, 
                        atPreDecFunc, 
                        HoareLoopInvariantRule.INSTANCE, pos, userConstraint);
            hoareLoopInv = null;
            loadedInsts  = null;
            return ourApp;
            
        }

        final SetOfRuleApp ruleApps =
            mediator.getBuiltInRuleApplications(currTacletName, pos);

        if (ruleApps.size() != 1) {
            if (ruleApps.size() < 1) {
                throw new BuiltInConstructionException
                (currTacletName +
                    " is missing. Most probably the binary "+
                    "for this built-in rule ist not in your path or " +
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

        Constraint userC = mediator.getUserConstraint().getConstraint();
        Services services = mediator.getServices();

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
            ourApp = ourApp.setPosInOccurrence(pos);
        }


        ourApp = constructInsts(ourApp, services);

        ourApp = ourApp.setIfFormulaInstantiations(ifSeqFormulaList,
                                                   services, userC);

        if (!ourApp.sufficientlyComplete()) {
            ourApp = ourApp.tryToInstantiate(currGoal, proof.getServices());
        }

        return ourApp;
    }



    /** 1st pass: only VariableSV */
    public static TacletApp parseSV1(TacletApp app, SchemaVariable sv,
                                     String value, Services services) {
        LogicVariable lv=new LogicVariable(new Name(value),
                                           app.getRealSort(sv, services));
        Term instance = TermFactory.DEFAULT.createVariableTerm(lv);
        return app.addCheckedInstantiation(sv, instance, services,true);
    }



    /** 2nd pass: all other SV */
    public static TacletApp parseSV2(TacletApp app, SchemaVariable sv,
                                     String value, Goal targetGoal) {        
        final Proof p = targetGoal.proof();
        final Services services = p.getServices();
        TacletApp result;
        if (sv.isVariableSV()) {
            // ignore -- already done
            result = app;
        } else if (sv.isProgramSV()) {
	    final ProgramElement pe = 
	        TacletInstantiationsTableModel.getProgramElement(
		    app, value, sv, services);
	    result = app.addCheckedInstantiation(sv, pe, services, true);
        } else if ( sv.isSkolemTermSV() ) {
	    result = app.createSkolemConstant ( value, sv, true, services );
        } else if (sv.isListSV()) {
            SetOfLocationDescriptor s = parseLocationList(value, targetGoal);
            result = app.addInstantiation(sv, s.toArray(), true);
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
        SetOfSchemaVariable uninsts = app.uninstantiatedVars();

        // first pass: add variables
        Iterator it = loadedInsts.iterator();
        while (it.hasNext()) {
            String s = (String) it.next();
            int eq = s.indexOf('=');
            String varname = s.substring(0, eq);
            String value = s.substring(eq+1, s.length());
            if (varname.startsWith(NameSV.NAME_PREFIX)) {
                app = app.addInstantiation(new NameSV(varname), new Name(value));
                continue;
            }

            SchemaVariable sv = lookupName(uninsts, varname);
            if (sv==null) {
//                throw new IllegalStateException(
//                    varname+" from \n"+loadedInsts+"\n is not in\n"+uninsts);
                System.err.println(varname+" from "+app.rule().name()+" is not in uninsts");
                continue;
            }

            if (sv.isVariableSV()) {
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
            String value = s.substring(eq+1, s.length());
            SchemaVariable sv = lookupName(uninsts, varname);
            if (sv==null) continue;
            app = parseSV2(app, sv, value, currGoal);
        }

        return app;
    }


    public static Term parseTerm(String value, Proof proof,
            Namespace varNS, Namespace progVar_ns) {
        try {
            return TermParserFactory.createInstance().
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


    public static SetOfLocationDescriptor parseLocationList(String value, Goal targetGoal) {
        SetOfLocationDescriptor result = null;
        Proof p = targetGoal.proof();
        Namespace varNS = p.getNamespaces().variables();
        NamespaceSet nss = new NamespaceSet(
            varNS,
            p.getNamespaces().functions(),
            p.getNamespaces().sorts(),
            new Namespace(),
            new Namespace(),
            targetGoal.getVariableNamespace(varNS));
        Services services = p.getServices();
        try{
            result = (new KeYParser(ParserMode.TERM,new KeYLexer(new StringReader(value),
                                             services.getExceptionHandler()),
                                null, TermFactory.DEFAULT, null, services,
                                nss, new AbbrevMap())).
                location_list();
        } catch (antlr.RecognitionException re) {
            throw new RuntimeException("Cannot parse location list "+value, re);
        } catch (antlr.TokenStreamException tse) {
            throw new RuntimeException("Cannot parse location list "+value, tse);
        }
        return result;
    }



    public static Term parseTerm(String value, Proof proof) {
        return parseTerm(value, proof, proof.getNamespaces().variables(),
                proof.getNamespaces().programVariables());
    }


    private SchemaVariable lookupName(SetOfSchemaVariable set, String name) {
        IteratorOfSchemaVariable it = set.iterator();
        while (it.hasNext()) {
            SchemaVariable v = it.next();
            if (v.name().toString().equals(name)) return v;
        }
        return null; // handle this better!
    }

    private class AppConstructionException extends Exception {

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

    private class BuiltInConstructionException extends Exception {

        BuiltInConstructionException(String s) {
            super(s);
    }
    }

}
