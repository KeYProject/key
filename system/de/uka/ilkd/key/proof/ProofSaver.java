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

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.EntryOfSchemaVariableAndInstantiationEntry;
import de.uka.ilkd.key.logic.op.IteratorOfEntryOfSchemaVariableAndInstantiationEntry;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PresentationFeatures;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.*;

/**
 * Saves a proof and provides useful methods for pretty printing
 * terms or programs.
 */
public class ProofSaver {

   protected IMain main;
   protected KeYMediator mediator;
   protected String filename;
   protected Proof proof;
   LogicPrinter printer;
   
   public ProofSaver(IMain main, String filename) {
      this.main = main;
      this.mediator = main.mediator();
      this.filename = filename;
      this.proof = mediator.getSelectedProof();
   }

   public StringBuffer writeLog(Proof p){
    StringBuffer logstr=new StringBuffer();
    //Advance the Logentries
    if(p.userLog==null)
        p.userLog = new Vector<String>();
    if(p.keyVersionLog==null)
        p.keyVersionLog = new Vector<String>();
    p.userLog.add(System.getProperty("user.name"));
    p.keyVersionLog.add(main.getInternalVersion());
    int s = p.userLog.size();
    for(int i=0; i<s; i++){
	logstr.append("(keyLog \""+i+"\" (keyUser \""+
            p.userLog.elementAt(i)+"\" ) (keyVersion \""+
            p.keyVersionLog.elementAt(i)+"\"))\n");
       }
    return logstr;
   }

   public String writeSettings(ProofSettings ps){
    	return new String ("\\settings {\n\""+ps.settingsToString()+"\"\n}\n");
   }
   public String save() {
      String errorMsg = null;
      FileOutputStream fos = null;
      PrintStream ps = null;

      try {
          fos = new FileOutputStream(filename);
          ps = new PrintStream(fos);


          Sequent problemSeq = proof.root().sequent();
          printer = createLogicPrinter(proof.getServices(), false);

          ps.println(writeSettings(proof.getSettings()));
          ps.print(proof.header());
          ps.println("\\problem {");
          printer.printSemisequent(problemSeq.succedent());
          ps.println(printer.result());
          ps.println("}\n");
   //                ps.println(mediator.sort_ns());
          ps.println("\\proof {");
          ps.println(writeLog(proof));
          printUserConstraints(ps);
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
          try {
	      if (fos != null) fos.close();
          } catch (IOException ioe) {
	      mediator.notify(new GeneralFailureEvent(ioe.toString()));
          }          
      }	  
      return errorMsg; // null if success
   }
   
   private String mc2Proof(MatchConditions mc) {
        if (mc != null) {
            Constraint c = mc.getConstraint();
            if (c instanceof EqualityConstraint && !c.isBottom()) {
                Services s = mediator.getServices();
                String res = "";
                Iterator<Metavariable> it = ((EqualityConstraint) c)
                        .restrictedMetavariables();
                while (it.hasNext()) {
                    Metavariable mv = it.next();
                    res = res + " (matchconstraint \"" + mv.name() + "="
                            + printTerm(c.getInstantiation(mv), s) + "\")";
                }
                return res;
            }
        }
        return "";
    }

    private String newNames2Proof(Node n) {
        String s = "";
        NameRecorder rec = n.getNameRecorder();
        if (rec == null) {
            return s;
        }
        ListOfName proposals = rec.getProposals();
        if (proposals.isEmpty()) {
            return s;
        }
        for (IteratorOfName it = proposals.iterator(); it.hasNext();) {
            s += "," + it.next();
        }
        return " (newnames \"" + s.substring(1) + "\")";
    }

    private void printUserConstraints(PrintStream ps) {
        ConstraintTableModel uCons = proof.getUserConstraint();
        Services s = mediator.getServices();

        if (uCons.getRowCount() > 0) {

            for (int i = 0; i < uCons.getRowCount(); i++) {
                ps.println("(userconstraint \"" + printTerm((Term) uCons
                        .getValueAt(i, 0), s)
                        + "=" + printTerm((Term) uCons.getValueAt(i, 1), s)
                        + "\")");
            }

        }

    }

   private void printSingleNode(Node node, String prefix, StringBuffer tree) {

      RuleApp appliedRuleApp = node.getAppliedRuleApp();
      if (appliedRuleApp == null && (proof.getGoal(node)!=null)) { // open goal
         tree.append(prefix); 
         tree.append("(opengoal \"");
         LogicPrinter logicPrinter = 
	     createLogicPrinter(proof.getServices(), false);

         logicPrinter.printSequent(node.sequent());
	 // WATCHOUT Woj: replaceAll... is necessary for the newly introduced backslash
	 // notation in the parser
         tree.append(printer.result().toString().replace('\n',' ').replaceAll("\\\\","\\\\\\\\"));
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
         tree.append(mc2Proof(((TacletApp)appliedRuleApp).matchConditions()));
         tree.append(newNames2Proof(node));
         tree.append(getInteresting(((TacletApp)appliedRuleApp).instantiations()));
         ListOfIfFormulaInstantiation l =
            ((TacletApp)appliedRuleApp).ifFormulaInstantiations();
         if (l != null) tree.append(ifFormulaInsts(node, l));
         tree.append("");
         userInteraction2Proof(node, tree);
         tree.append(")\n");
      }      
        
      if (appliedRuleApp instanceof BuiltInRuleApp) {
        tree.append(prefix); 
      	tree.append("(builtin \"");
      	tree.append(appliedRuleApp.rule().name().toString());
      	tree.append("\"");        
        tree.append(posInOccurrence2Proof(node.sequent(), 
                                          appliedRuleApp.posInOccurrence()));
        tree.append(newNames2Proof(node));

        if (appliedRuleApp.rule() instanceof UseOperationContractRule) {
            RuleJustificationBySpec ruleJusti = (RuleJustificationBySpec) 
                            proof.env().getJustifInfo()
                                       .getJustification(appliedRuleApp, 
                                                         proof.getServices());

            tree.append(" (contract \"");
            tree.append(ruleJusti.getSpec().toString());
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
         tree.append("(branch \" "+child.getNodeInfo().getBranchLabel().replaceAll("\\\\","\\\\\\\\")+"\"\n");
	 collectProof(child, prefix+"   ", tree);
         tree.append(prefix+")\n");
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
      IteratorOfEntryOfSchemaVariableAndInstantiationEntry pairIt =
         inst.interesting().entryIterator();

      while (pairIt.hasNext()) {
         EntryOfSchemaVariableAndInstantiationEntry pair = pairIt.next();
         SchemaVariable var = pair.key();
	 s += " (inst \""+var.name()+"=";
	 Object value = pair.value();
	 if (value instanceof TermInstantiation) {
	     s += printTerm(((TermInstantiation) value).getTerm(), 
	                    proof.getServices());
	 }
         else
	 if (value instanceof ProgramInstantiation) {
	     ProgramElement pe = 
		 ((ProgramInstantiation) value).getProgramElement();
	     s += printProgramElement(pe);
	 }
         else
	 if (value instanceof NameInstantiationEntry) {
	     s += ((NameInstantiationEntry) value).getInstantiation();
	 }
         else 
         if (value instanceof ListInstantiation) {
             ListOfObject l = (ListOfObject) ((ListInstantiation) value).getInstantiation();
             s += printListInstantiation(l, proof.getServices());
         }
         else
             throw new RuntimeException("Saving failed.\n"+
           "FIXME: Unhandled instantiation type: " +  value.getClass());
	 s += "\")";
      }
      // WATCHOUT: Woj: again, quote backslashes
      s = s.replaceAll("\\\\","\\\\\\\\");
      return s;
   }
   
   

   public static String printListInstantiation(ListOfObject l, Services serv) {
       final StringBuffer sb = new StringBuffer("{");
       final IteratorOfObject it = l.iterator();
       while (it.hasNext()) {
           final Object next = it.next();
           if (next instanceof LocationDescriptor) {
               sb.append(printLocationDescriptor(
	           (LocationDescriptor)next, serv));
           } else {
               throw new RuntimeException("Unexpected entry in " +
                        "ListInstantiation");               
           }
           if (it.hasNext()) sb.append(",");
       }
       sb.append("}");
       return sb.toString();
   }

   public String ifFormulaInsts(Node node, ListOfIfFormulaInstantiation l) {
      String s ="";
      IteratorOfIfFormulaInstantiation it = l.iterator();
      while (it.hasNext()) {
         IfFormulaInstantiation iff = it.next();
         if (iff instanceof IfFormulaInstSeq) {
            ConstrainedFormula f = iff.getConstrainedFormula();
            s+= " (ifseqformula \"" + 
                node.sequent().formulaNumberInSequent(
                        ((IfFormulaInstSeq)iff).inAntec(),f) + 
                        "\")";
            }
            else
                if (iff instanceof IfFormulaInstDirect) {
                    s += " (ifdirectformula \"" + iff.getConstrainedFormula()
                        + "\")";
                }
                else throw new RuntimeException("Unknown If-Seq-Formula type");
        }
        return s;
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


    public static StringBuffer printLocationDescriptor(LocationDescriptor loc,
            Services serv) {
        StringBuffer result;
        LogicPrinter logicPrinter = createLogicPrinter(serv, false);
        try {
            logicPrinter.printLocationDescriptor(loc);
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
            else 
                if (val==null){
                    return null;
                }
                else {
                    System.err.println("Don't know how to prettyprint "+val.getClass());
                    // try to String by chance
                    return val.toString();
                }
    }


    private static LogicPrinter createLogicPrinter(Services serv, 
            boolean shortAttrNotation) {

        NotationInfo ni = NotationInfo.createInstance();
        LogicPrinter p = null;

        if (serv != null) {
            PresentationFeatures.modifyNotationInfo(ni,
                    serv.getNamespaces().functions());
        }
        p =  new LogicPrinter(new ProgramPrinter(null), ni, (shortAttrNotation ? serv : null), true);
        return p;
    }


}
