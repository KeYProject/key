// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Iterator;
import java.util.Properties;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.NameInstantiationEntry;
import de.uka.ilkd.key.rule.inst.ProgramInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.TermInstantiation;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Saves a proof and provides useful methods for pretty printing
 * terms or programs.
 */
public class ProofSaver {

   //protected IMain main;
   //protected KeYMediator mediator;
   final protected String filename;
   final protected Proof proof;
   final protected String internalVersion;
   
   LogicPrinter printer;
   
   public ProofSaver(Proof proof, String filename, String internalVersion) {
      //this.main = main;
      //this.mediator = main.mediator();
      this.filename = filename;
      this.proof = proof;//mediator.getSelectedProof();
      this.internalVersion = internalVersion;
      
   }

   public StringBuffer writeLog(Proof p){
    StringBuffer logstr=new StringBuffer();
    //Advance the Logentries
    if(p.userLog==null)
        p.userLog = new Vector<String>();
    if(p.keyVersionLog==null)
        p.keyVersionLog = new Vector<String>();
    p.userLog.add(System.getProperty("user.name"));
    p.keyVersionLog.add(internalVersion);
    int s = p.userLog.size();
    for(int i=0; i<s; i++){
	logstr.append("(keyLog \""+i+"\" (keyUser \""+
            p.userLog.elementAt(i)+"\" ) (keyVersion \""+
            p.keyVersionLog.elementAt(i)+"\"))\n");
       }
    return logstr;
   }

   public String writeSettings(ProofSettings ps){
    	return new String ("\\settings {\n\""+escapeCharacters(ps.settingsToString())+"\"\n}\n");
   }
   
   public String save() throws IOException {
      return save(new FileOutputStream(filename));
   }
   
   public String save(OutputStream out) throws IOException {
      String errorMsg = null;
      PrintWriter ps = null;
      
      try {
          ps = new PrintWriter(out, true);
          printer = createLogicPrinter(proof.getServices(), false);
          
          //settings
          ps.println(writeSettings(proof.getSettings()));
          
          //declarations of symbols, sorts
          String header = proof.header();
          header = makePathsRelative(header);
          ps.print(header);

          //\problem or \proofObligation
          ProofOblInput po = proof.getServices().getSpecificationRepository().getProofOblInput(proof);
          if(po instanceof IPersistablePO) {
              Properties properties = new Properties();
              ((IPersistablePO)po).fillSaveProperties(properties);
              StringWriter writer = new StringWriter();
              try {
                 properties.store(writer, "Proof Obligation Settings");
                 ps.println("\\proofObligation \"" +escapeCharacters(writer.toString()) + "\";\n");
              }
              finally {
                writer.close();
              }
          } else {
              Sequent problemSeq = proof.root().sequent();
              ps.println("\\problem {");
              printer.printSemisequent(problemSeq.succedent());
              ps.println(printer.result());
              ps.println("}\n");
          }

          //\proof
          ps.println("\\proof {");
          ps.println(writeLog(proof));
          ps.println("(autoModeTime \"" + proof.getAutoModeTime() + "\")\n");
          ps.println(node2Proof(proof.root()));
          ps.println("}");

      } catch (IOException ioe) {
          errorMsg = "Could not save \n"+filename+".\n";
          errorMsg += ioe.toString();	    
      } catch (NullPointerException npe) {
          errorMsg = "Could not save \n"+filename+"\n";
          errorMsg += "No proof present?";
          npe.printStackTrace();
      } catch (Exception e) {
          errorMsg = e.toString();
          e.printStackTrace();
      } finally {
          //try {
	      if (out != null) out.close();
	      if (ps != null) {
		  ps.flush();
		  ps.close();
	      }
          //} catch (IOException ioe) {
	    //  mediator.notify(new GeneralFailureEvent(ioe.toString()));
          //}          
      }	  
      return errorMsg; // null if success
   }
   
 

   /** Searches in the header for absolute paths to Java files and tries to replace them
    * by paths relative to the proof file to be saved.
    */
   private String makePathsRelative(String header) {
       final String[] search = new String[]{"\\javaSource","\\bootclasspath","\\classpath"};
       String basePath = null;
       String tmp = header;
       final char sep = File.separatorChar;
       try {
           basePath = (new File(filename)).getCanonicalPath();
           final int indexOfSep = basePath.lastIndexOf(sep) >= 0 ? basePath.lastIndexOf(sep) : basePath.length();
           basePath = basePath.substring(0, indexOfSep);
           // locate filenames in header
           for (String s: search){
               int i = tmp.indexOf(s);
               if (i == -1) continue; // entry not in file

               // put in everything before the keyword
               // bugfix #1138: changed i-1 to i
               String tmp2 = tmp.substring(0, i);
               String relPathString = "";
               i += s.length();
               int l = tmp.indexOf(";",i);
               
               // there may be more than one path
               while (0 <= tmp.indexOf("\"",i) && tmp.indexOf("\"",i) < l) {
                   // path is always put in quotation marks
                   int k = tmp.indexOf("\"",i)+1;
                   int j = tmp.indexOf("\"", k);

                   // add new relative path
                   final String absPath = tmp.substring(k,j);
                   final String relPath = MiscTools.makeFilenameRelative(absPath, basePath);
                   relPathString = relPathString+" \"" + relPath +"\"";
                   i = j+1;
               }
               tmp2 = tmp2 + s + relPathString + ";";

               // put back in the rest
               tmp = tmp2 + (i < tmp.length()? tmp.substring(l+1,tmp.length()): "");
           }
       } catch (IOException e) {
           e.printStackTrace();
       }
       return tmp;
   }

    private String newNames2Proof(Node n) {
        String s = "";
        NameRecorder rec = n.getNameRecorder();
        if (rec == null) {
            return s;
        }
        ImmutableList<Name> proposals = rec.getProposals();
        if (proposals.isEmpty()) {
            return s;
        }
        for (Name proposal : proposals) {
            s += "," + proposal;
        }
        return " (newnames \"" + s.substring(1) + "\")";
    }


   private void printSingleNode(Node node, String prefix, StringBuffer tree) {

      RuleApp appliedRuleApp = node.getAppliedRuleApp();
      if (appliedRuleApp == null && (proof.getGoal(node)!=null)) { // open goal
         tree.append(prefix); 
         tree.append("(opengoal \"");
         LogicPrinter logicPrinter = 
	     createLogicPrinter(proof.getServices(), false);

         logicPrinter.printSequent(node.sequent());
         tree.append(escapeCharacters(printer.result().toString().replace('\n',' ')));
         tree.append("\")\n");
         return;
      }

      if (appliedRuleApp instanceof TacletApp) {
         tree.append(prefix); 
         tree.append("(rule \"");
         tree.append(appliedRuleApp.rule().name());	
         tree.append("\"");
         tree.append(posInOccurrence2Proof(node.sequent(),
                                           appliedRuleApp.posInOccurrence()));
         tree.append(newNames2Proof(node));
         tree.append(getInteresting(((TacletApp)appliedRuleApp).instantiations()));
         ImmutableList<IfFormulaInstantiation> l =
            ((TacletApp)appliedRuleApp).ifFormulaInstantiations();
         if (l != null) tree.append(ifFormulaInsts(node, l));
         tree.append("");
         userInteraction2Proof(node, tree);
         tree.append(")\n");
      }      
        
      if (appliedRuleApp instanceof IBuiltInRuleApp) {
        tree.append(prefix); 
      	tree.append("(builtin \"");
      	tree.append(appliedRuleApp.rule().name().toString());
      	tree.append("\"");        
        tree.append(posInOccurrence2Proof(node.sequent(), 
                                          appliedRuleApp.posInOccurrence()));
        tree.append(newNames2Proof(node));
        tree.append(builtinRuleIfInsts(node, 
        	                       ((IBuiltInRuleApp)appliedRuleApp).ifInsts()));

        if (appliedRuleApp.rule() instanceof UseOperationContractRule 
            || appliedRuleApp.rule() instanceof UseDependencyContractRule) {
            RuleJustification ruleJusti = 
                            proof.env().getJustifInfo()
                                       .getJustification(appliedRuleApp, 
                                                         proof.getServices());
            
            assert ruleJusti instanceof RuleJustificationBySpec : 
                "Please consult bug #1111 if this fails.";
            
            RuleJustificationBySpec ruleJustiBySpec = (RuleJustificationBySpec) ruleJusti;
            tree.append(" (contract \"");
            tree.append(ruleJustiBySpec.getSpec().getName());
            tree.append("\")");
        }

        tree.append(")\n");
      }
   }


   private StringBuffer collectProof(Node node, String prefix, 
                                     StringBuffer tree) {       

      printSingleNode(node, prefix, tree);
      Iterator<Node> childrenIt = null;
      
      while (node.childrenCount() == 1) {
          childrenIt = node.childrenIterator();
          node = childrenIt.next();
          printSingleNode(node, prefix, tree);
      }


      if (node.childrenCount() == 0) return tree;

      childrenIt = node.childrenIterator();

      while (childrenIt.hasNext()) {
         Node child = childrenIt.next();
         tree.append(prefix);            
         String branchLabel = child.getNodeInfo().getBranchLabel();
         
         // The branchLabel is ignored when reading in the proof,
         // print it if we have it, ignore it otherwise. (MU)
         if (branchLabel == null) {
             tree.append("(branch\n");
         } else {
             tree.append("(branch \"" + escapeCharacters(branchLabel) + "\"\n");
         }
         
         collectProof(child, prefix + "   ", tree);
         tree.append(prefix + ")\n");
      }

      return tree;
   }

  
   private void userInteraction2Proof(Node node, StringBuffer tree) {
       if (node.getNodeInfo().getInteractiveRuleApplication()) 
           tree.append(" (userinteraction)");
   }


   public String node2Proof(Node node) {
       StringBuffer tree=new StringBuffer();
       String s = "(branch \"dummy ID\"\n"+collectProof(node, "",tree)+")\n"; 
       return s;
   }


    public String posInOccurrence2Proof(Sequent seq, PosInOccurrence pos) {
        if (pos == null) return "";
        return " (formula \""+seq.formulaNumberInSequent(pos.isInAntec(),
                pos.constrainedFormula())+"\")"+
                posInTerm2Proof(pos.posInTerm());
    }

   

   public String posInTerm2Proof(PosInTerm pos) {
      if (pos == PosInTerm.TOP_LEVEL) return "";
      String s = " (term \"";
      String list = pos.integerList(pos.reverseIterator()); // cheaper to read in
      s = s + list.substring(1,list.length()-1); // chop off "[" and "]"
      s = s + "\")";
      return s;
   }
   
   


   public String getInteresting(SVInstantiations inst) {
//System.err.println(inst);   
      String s = "";
      Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> pairIt =
         inst.interesting().entryIterator();

      while (pairIt.hasNext()) {
         ImmutableMapEntry<SchemaVariable,InstantiationEntry> pair = pairIt.next();
         SchemaVariable var = pair.key();
	 
         String singleInstantiation = var.name()+ "="; 
	 Object value = pair.value();
	 if (value instanceof TermInstantiation) {
	     singleInstantiation += printTerm(((TermInstantiation) value).getTerm(), 
	                    proof.getServices());
	 }
         else
	 if (value instanceof ProgramInstantiation) {
	     ProgramElement pe = 
		 ((ProgramInstantiation) value).getProgramElement();
	     singleInstantiation += printProgramElement(pe);
	 }
         else
	 if (value instanceof NameInstantiationEntry) {
	     singleInstantiation += ((NameInstantiationEntry) value).getInstantiation();
	 }
         else 
             throw new RuntimeException("Saving failed.\n"+
           "FIXME: Unhandled instantiation type: " +  value.getClass());
	 
	 singleInstantiation = escapeCharacters(singleInstantiation);
	
	 s += " (inst \"" + singleInstantiation + "\")";
      }
      
      return s;
   }
   

   public String ifFormulaInsts(Node node, ImmutableList<IfFormulaInstantiation> l) {
      String s ="";
       for (IfFormulaInstantiation aL : l) {
           IfFormulaInstantiation iff = aL;
           if (iff instanceof IfFormulaInstSeq) {
               SequentFormula f = iff.getConstrainedFormula();
               s += " (ifseqformula \"" +
                       node.sequent().formulaNumberInSequent(
                               ((IfFormulaInstSeq) iff).inAntec(), f) +
                       "\")";
           } else if (iff instanceof IfFormulaInstDirect) {

               final String directInstantiation = printTerm(iff.getConstrainedFormula().formula(),
                       node.proof().getServices()).toString();

               s += " (ifdirectformula \"" + escapeCharacters(directInstantiation) + "\")";
           } else throw new RuntimeException("Unknown If-Seq-Formula type");
       }
      
        return s;
    }
   
   
   public String builtinRuleIfInsts(Node node, 
	   			    ImmutableList<PosInOccurrence> ifInsts) {
       String s = "";
       for(PosInOccurrence ifInst : ifInsts) {
	   s += " (ifInst \"\" ";
	   s += posInOccurrence2Proof(node.sequent(), ifInst);
	   s += ")";
       }
       return s;
    }   


    /**
     * double escapes quotation marks and backslashes to be storeable in a text file 
     * @param toEscape the String to double escape
     * @return the escaped version of the string
     */
    public static String escapeCharacters(String toEscape) {
	
	String result = toEscape;	
	
	// first escape backslash
	result = result.replaceAll("\\\\","\\\\\\\\");
	// then escape quotation marks
	result = result.replaceAll("\"", "\\\\\"");

	return result;
    }

    public static String printProgramElement(ProgramElement pe) {
        java.io.StringWriter sw = new java.io.StringWriter();
        ProgramPrinter prgPrinter = new ProgramPrinter(sw);
        try{
            pe.prettyPrint(prgPrinter);
        } catch(IOException ioe) {System.err.println(ioe);}
        return sw.toString();
    }


    public static StringBuffer printTerm(Term t, Services serv) {
        return printTerm(t, serv, false);
    }


    public static StringBuffer printTerm(Term t, Services serv, 
            boolean shortAttrNotation) {
        StringBuffer result;
        LogicPrinter logicPrinter = createLogicPrinter(serv, shortAttrNotation);
        try {
            logicPrinter.printTerm(t);
        } catch(IOException ioe) {
            System.err.println(ioe);
        }
        result = logicPrinter.result();
        if (result.charAt(result.length()-1) == '\n')
            result.deleteCharAt(result.length()-1);
        return result;
    }


    public static String printAnything(Object val, Services services) {
        if (val instanceof ProgramElement) {
            return printProgramElement((ProgramElement) val);
        }
        else
            if (val instanceof Term) {
                return printTerm((Term) val, services, true).toString();
            }
            else if (val instanceof Sequent) {
                return printSequent((Sequent) val, services);
            } else if (val==null){
                    return null;
            }
            else {
                System.err.println("Don't know how to prettyprint "+val.getClass());
                // try to String by chance
                return val.toString();
            }
    }


    private static String printSequent(Sequent val, Services services) {
        LogicPrinter printer = createLogicPrinter(services, services == null);
        printer.printSequent(val);
        return printer.toString();
    }

    private static LogicPrinter createLogicPrinter(Services serv, 
            boolean shortAttrNotation) {

        NotationInfo ni = new NotationInfo();
        LogicPrinter p = null;

        p =  new LogicPrinter(new ProgramPrinter(null), ni, (shortAttrNotation ? serv : null), true);
        return p;
    }
}
