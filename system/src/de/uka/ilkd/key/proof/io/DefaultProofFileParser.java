// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.io;

import java.io.StringReader;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.KeYMediator;
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
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;

/**
 * Default implementation of {@link IProofFileParser}.
 * @author Martin Hentschel
 */
public class DefaultProofFileParser implements IProofFileParser {

    private static final String ERROR_LOADING_PROOF_LINE = "Error loading proof.\n";
    private static final String NOT_APPLICABLE = " not available or not applicable in this context.";

    private final DefaultProblemLoader loader;
   private Proof proof = null;
   private Iterator<Node> children = null;

   private Node currNode = null;
   private Goal currGoal = null;
   private String currTacletName = null;
   private int currFormula = 0;
   private PosInTerm currPosInTerm = PosInTerm.getTopLevel();
   private Contract currContract = null;
   private Stack<Iterator<Node>> stack = new Stack<Iterator<Node>>();
   private LinkedList<String> loadedInsts = null;
   private ImmutableList<IfFormulaInstantiation> ifFormulaList = ImmutableSLList.<IfFormulaInstantiation>nil();
   private ImmutableList<PosInOccurrence> builtinIfInsts;
   private int currIfInstFormula;
   private PosInTerm currIfInstPosInTerm;
   private String status = "";


   private KeYMediator mediator;
   
   
   /** a value == 1 means the current branch is ignored; a value > 1 means that the "skipBranch - 1" parent branch of the
    *  current branch is ignored.
    *  a value == 0 means that no branch is ignored 
    */
   private int skipBranch;

   private List<Throwable> errors = new LinkedList<Throwable>();


   public DefaultProofFileParser(DefaultProblemLoader loader, Proof proof, KeYMediator mediator) {
      super();
      this.proof = proof;
      this.mediator = mediator;
      this.loader = loader;
      currNode = proof.root(); // initialize loader
      children = currNode.childrenIterator(); // --"--
   }

   public DefaultProofFileParser(Proof proof, KeYMediator mediator) {
       this(null, proof, mediator);
   }

   /**
    * Communicates a non-fatal condition to the caller. Empty string
    * means everything is OK. The message will be displayed to the user
    * in the GUI after the proof has been parsed.
    */
   public String getStatus() {
       return status;
   }


// note: Expressions without parameters only emit the endExpr signal
   @Override
   public void beginExpr(char id, String s) throws ProblemLoaderException {

       //start no new commands until the ignored branch closes
       //count sub-branches though
       if (skipBranch > 0 && id != 'b') return;
       
       switch (id) {
       case 'b' :
           stack.push(children);
           if (children.hasNext()) currNode = children.next();
           if (skipBranch > 0) {
               skipBranch ++;
           }
           break;
  case 'r' :
           if (currNode == null) currNode = children.next();
           // otherwise we already fetched the node at branch point
           currGoal      = proof.getGoal(currNode);
           mediator.getSelectionModel().setSelectedGoal(currGoal);
           currTacletName= s;
           // set default state
           currFormula   = 0;
           currPosInTerm = PosInTerm.getTopLevel();
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
           if (loadedInsts == null) loadedInsts = new LinkedList<String>();
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
           currPosInTerm = PosInTerm.getTopLevel();
           builtinIfInsts = null;
           break;
       case 'c' : //contract
           currContract = proof.getServices().getSpecificationRepository().getContractByName(s);
           if(currContract == null) {
               throw new ProblemLoaderException(loader, "Error loading proof: contract \"" + s + "\" not found.");
           }
           break;
       case 'x' : //ifInst (for built in rules)
           if(builtinIfInsts == null) {
        builtinIfInsts = ImmutableSLList.<PosInOccurrence>nil();
           }
           currIfInstFormula = 0;
           currIfInstPosInTerm = PosInTerm.getTopLevel();
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


   @Override
   public void endExpr(char id, int linenr) throws ProblemLoaderException {
       //System.out.println("end "+id);

       //read no new commands until ignored branch closes
       if (skipBranch > 0 && id != 'b') return;

       switch (id) {
       case 'b' :
           children = stack.pop();
           if (skipBranch > 0) {
               skipBranch--;
           }
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
               skipBranch = 1;
               reportError(ERROR_LOADING_PROOF_LINE+"Line "+linenr+
                   ", goal "+currGoal.node().serialNr()+
                   ", rule "+currTacletName+NOT_APPLICABLE,e);
           } catch (AssertionError e) {
               skipBranch = 1;
               reportError(ERROR_LOADING_PROOF_LINE+"Line "+linenr+
                   ", goal "+currGoal.node().serialNr()+
                   ", rule "+currTacletName+NOT_APPLICABLE,e);
           }
           break;
       case 'n' :
           try {
               IBuiltInRuleApp app = constructBuiltinApp();
              if (!app.complete()) {
                 app = app.tryToInstantiate(currGoal);
              }
               currGoal.apply(app);
               children = currNode.childrenIterator();
               currNode = null;
           } catch (SkipSMTRuleException e) {
               // silently continue; status will be reported via polling
           } catch (BuiltInConstructionException e) {
               skipBranch = 1;
               reportError(ERROR_LOADING_PROOF_LINE+"Line "+linenr+
                   ", goal "+currGoal.node().serialNr()+
                   ", rule "+currTacletName+NOT_APPLICABLE,e);
           } catch (RuntimeException e) {
               skipBranch = 1;
               reportError(ERROR_LOADING_PROOF_LINE+"Line "+linenr+
                   ", goal "+currGoal.node().serialNr()+
                   ", rule "+currTacletName+NOT_APPLICABLE,e);
           } catch (AssertionError e) {
               skipBranch = 1;
               reportError(ERROR_LOADING_PROOF_LINE+"Line "+linenr+
                   ", goal "+currGoal.node().serialNr()+
                   ", rule "+currTacletName+NOT_APPLICABLE,e);
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
//        System.out.println("formula: " + currIfInstFormula);
//        System.out.println("term: " + currIfInstPosInTerm);
               skipBranch = 1;
               reportError(ERROR_LOADING_PROOF_LINE+"Line "+linenr+
                   ", goal "+currGoal.node().serialNr()+
                   ", rule "+currTacletName+NOT_APPLICABLE,e);
           } catch (AssertionError e) {
               skipBranch = 1;
               reportError(ERROR_LOADING_PROOF_LINE+"Line "+linenr+
                   ", goal "+currGoal.node().serialNr()+
                   ", rule "+currTacletName+NOT_APPLICABLE,e);
           }
           break;
       }

   }


   
   private void reportError(String string, Throwable e) {       
       status = "Errors while reading the proof. Not all branches could be load successfully.";
       errors.add(new ProblemLoaderException(loader, string, e));
   }

   /** 
    * returns list of errors that have been reported during parsing
    * @return list of errors
    */
   @Override
   public List<Throwable> getErrors() {
       return errors;
   }
   
   public void loadPreferences(String preferences) {
       final ProofSettings proofSettings = ProofSettings.DEFAULT_SETTINGS;
       proofSettings.loadSettingsFromString(preferences);
   }

   /**
    * Constructs rule application for UpdateSimplification from
    * current parser information
    *
    * @return current rule application for updateSimplification
    */
   private IBuiltInRuleApp constructBuiltinApp()
                              throws SkipSMTRuleException,
                                     BuiltInConstructionException {

        if ("SMTRule".equals(currTacletName)) {
            status = "Your proof has been loaded, but SMT solvers have not been run";
            throw new SkipSMTRuleException();
        }


     IBuiltInRuleApp ourApp = null;
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
          AbstractContractRuleApp contractApp = null;

          BuiltInRule useContractRule;
          if (currContract instanceof OperationContract) {
             useContractRule = UseOperationContractRule.INSTANCE;
             contractApp = (((UseOperationContractRule)useContractRule).createApp(pos)).setContract(currContract);
          }
          else {
             useContractRule = UseDependencyContractRule.INSTANCE;
             contractApp = (((UseDependencyContractRule)useContractRule).createApp(pos)).setContract(currContract);
          }
          
          if (contractApp.check(currGoal.proof().getServices()) == null) {
              throw new BuiltInConstructionException
              ("Cannot apply contract: " + currContract);
          } else {
              ourApp = contractApp;
          }
          
           currContract = null;
           if(builtinIfInsts != null) {
               ourApp = ourApp.setIfInsts(builtinIfInsts);
        builtinIfInsts = null;
           }
           return ourApp;
       }

       final ImmutableSet<IBuiltInRuleApp> ruleApps =
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
       ourApp = ruleApps.iterator().next();
       builtinIfInsts = null;
       return ourApp;
   }

   private TacletApp constructApp() throws AppConstructionException {
       TacletApp ourApp = null;
       PosInOccurrence pos = null;

       Taclet t = proof.env().getInitConfig().lookupActiveTaclet(new Name(currTacletName));
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
       Term instance = services.getTermFactory().createTerm(lv);
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
          app.getProgramElement(value, sv, services);
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
       Iterator<String> it = loadedInsts.iterator();
       while (it.hasNext()) {
           String s = it.next();
           int eq = s.indexOf('=');
           String varname = s.substring(0, eq);
           String value = s.substring(eq+1, s.length());

           SchemaVariable sv = lookupName(uninsts, varname);
           if (sv==null) {
//               throw new IllegalStateException(
//                   varname+" from \n"+loadedInsts+"\n is not in\n"+uninsts);
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
           String s = it.next();
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

    private static class SkipSMTRuleException extends Exception {

        private static final long serialVersionUID = -2932282883810135168L;

    }

}