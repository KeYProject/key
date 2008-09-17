// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.reuse;

import java.util.Hashtable;
import java.util.LinkedList;
import java.util.Vector;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.*;
import de.uka.ilkd.key.util.ExtList;

public class ReusePoint implements Comparable {

   Node templateNode;
   Goal targetGoal;
   int score = 0;
   PosInOccurrence targetPos;
   RuleApp templateApp;
   RuleApp reuseApp;
   /** the rule involved is not part of the standard set */
   private boolean goalLocalRule = false;
   
   private String s = "";

   private static Logger reuseLogger = Logger.getLogger("key.proof.reuse");
   
   
   private ReusePoint(ReusePoint other) {
      this.templateNode = other.templateNode;
      this.targetGoal = other.targetGoal;
      this.goalLocalRule = other.goalLocalRule;
      templateApp = templateNode.getAppliedRuleApp();
   }
   
   public ReusePoint(Node templateNode, Goal targetGoal) {
      this.templateNode = templateNode;
      this.targetGoal = targetGoal;
      templateApp = templateNode.getAppliedRuleApp();
   }


   public ReusePoint initialize(PosInOccurrence targetPos, 
                                RuleApp tentativeApp,
                                KeYMediator medi) {
      ReusePoint result = new ReusePoint(this);
      result.setTargetPos(targetPos);
      RuleApp targetApp = result.getTargetApp(tentativeApp, medi);
      if (targetApp == null) return null;
      result.setReuseApp(targetApp);
      result.compare(result.sourceTerm(), targetPos.subTerm());
      if (templateApp instanceof TacletApp) {
          result.compareIf((TacletApp)templateApp, (TacletApp)targetApp);
      }
      return result;
   }
   

   public ReusePoint initializeNoFind(RuleApp tentativeApp,
                                      KeYMediator medi) {
      ReusePoint result = new ReusePoint(this);
      RuleApp targetApp = result.getTargetApp(tentativeApp, medi);
      if (targetApp == null) return null;
      result.setReuseApp(targetApp);
      result.compareNoFind();
      return result;
   }
   
   
   
   public Goal target() {
      return targetGoal;
   }

   public Node source() {
      return templateNode;
   }
   
   public RuleApp getApp() {
      return templateApp;
   }
   
   public Term sourceTerm() {
      return templateApp.posInOccurrence().subTerm();
   }
   
   private void setTargetPos(PosInOccurrence pos) {
      this.targetPos = pos;
   }

   public PosInOccurrence getTargetPos() {
      return targetPos;
   }
   
   private void setReuseApp(RuleApp app) {
      reuseApp = app;
   }

   public RuleApp getReuseApp() {
      return reuseApp;
   }
   
   public ListOfName getNameProposals() {
       return templateNode.getNameRecorder().getProposals();
   }

   public void setGoalLocal(boolean b) {
       goalLocalRule = b;
   }
   
   private RuleApp getTargetApp(RuleApp tentativeApp, KeYMediator medi) {
      if (templateApp instanceof TacletApp) {
         TacletApp result = (TacletApp) tentativeApp;

         // 0th pass
         SVInstantiations insts = ((TacletApp)templateApp).instantiations();
	 IteratorOfSchemaVariable it = insts.svIterator();
         while (it.hasNext()) {
             SchemaVariable sv = it.next();
             if (sv instanceof NameSV) {
                 result = result.addInstantiation(
                     new NameSV(sv.name()), (Name)insts.getInstantiation(sv));
             } else continue;
         }
         




         // 1st pass
	 it = result.uninstantiatedVars().iterator();
	 while (it.hasNext()) {
            SchemaVariable sv = it.next();
            SchemaVariable svTemplate;
            
            if (goalLocalRule) {
                svTemplate = insts.lookupVar(sv.name());
            } else {
                svTemplate = sv;
            }
            
            String text = "";
            if (sv.isVariableSV()) {
                Object o = insts.getInstantiation(svTemplate);
                reuseLogger.info(result.rule().name()+
                    ": Copying instantiation of "+ o + " for "+ sv);

                if (o == null) {
                    text = 
                        nameSuggestion(sv, medi.getServices(), (TacletApp)tentativeApp);
                } else {
                    try{                    
                        text = ProofSaver.printTerm((Term)o, 
			    templateNode.proof().getServices()).toString();
                    } catch(Exception e) {
                        System.err.println("Missing "+sv+" from "+tentativeApp.rule().name());
                        return null;
                    }              
                }
                result = ProblemLoader.parseSV1(result, sv, text, 
                                                medi.getServices());
	    } else {
                // leave for 2nd pass
            }
         }

         // 2nd pass
	 it = result.uninstantiatedVars().iterator();
	 while (it.hasNext()) {
            SchemaVariable sv = it.next();
            SchemaVariable svTemplate;
            if (goalLocalRule) {
                svTemplate = insts.lookupVar(sv.name());
            } else {
                svTemplate = sv;
            }
            
            InstantiationEntry o = insts.getInstantiationEntry(svTemplate);
            
            if (result != null) {
                reuseLogger.info(result.rule().name()+
                        ": Copying instantiation of "+ o + " for "+ sv);
            }
                               
            String text = "";
            if (o instanceof TermInstantiation) {
               Term t = ((TermInstantiation)o).getTerm();
               text = ProofSaver.printTerm(t, 
		   templateNode.proof().getServices()).toString();
               if (t.op() instanceof Metavariable) {
                   continue; // will be instantiated elsewhere
                             // with the name proposal from the 0th pass
               }
            } else
            if (o instanceof ProgramInstantiation) {
               text = ProofSaver.printProgramElement(
                   ((ProgramInstantiation)o).getProgramElement());
            } else 
	    if (o instanceof ListInstantiation) {
               text = ProofSaver.printListInstantiation(
                   ((ListInstantiation)o).getList(), 
		   templateNode.proof().getServices());
            } else
	    if (o instanceof ListInstantiation) {
               text = ProofSaver.printListInstantiation(
                   ((ListInstantiation)o).getList(), 
		   templateNode.proof().getServices());
            } else
            if (o==null) {
//               throw new IllegalStateException(
//                   "Null InstantiationEntry for "+sv+" in "+templateApp);
                text = nameSuggestion(sv, medi.getServices(), 
                        (TacletApp)tentativeApp);                
            } else {
               System.err.println("What the hell is this instantiation? "+
                  sv+" of type "+o.getClass());
               text = nameSuggestion(sv, medi.getServices(), 
                       (TacletApp) tentativeApp);
            }
            if (text == null) {
                return null;
            }
            try{
                result = ProblemLoader.parseSV2(result, sv, text, targetGoal);
            } catch(IllegalInstantiationException e) {
                result = null;
            }
         }

         return result;


      } else if (templateApp instanceof BuiltInRuleApp) {
         IteratorOfRuleApp it = targetGoal.ruleAppIndex().
            getBuiltInRule(targetGoal, targetPos, 
               medi.getUserConstraint().getConstraint()).iterator();
         RuleApp result = null;
         RuleApp tmp;
         while (it.hasNext()) {
            tmp = it.next();
            if (tmp.rule().equals(templateApp.rule())) {
               if (result != null) throw new RuntimeException(templateApp.rule().name()+
                  ": found more than 1 app");
               else result = tmp;
            }
         }
         if (result == null) System.err.println(templateApp.rule().name()+
            ": found 0 apps -- too bad!");
         return result;
      } else throw new RuntimeException(templateApp.rule().name()+
         ": neither TacletApp nor BuiltinRuleApp");
   }

   private String nameSuggestion(SchemaVariable sv, 
           Services services, TacletApp app) {
       String text;
       if (sv.isProgramSV()) {
           text = services.
           getVariableNamer().getSuggestiveNameProposalForProgramVariable((ProgramSV)sv, app, 
                   targetGoal, services, SLListOfString.EMPTY_LIST);
       } else {
           text = VariableNameProposer.DEFAULT.getNameProposal(sv.name().toString().replaceAll("#",""), 
                   services, targetGoal.node());
       }
       return text;
   }
   
   
   
   public int score() {
      return score;
   }
   
   public boolean notGoodEnough() {
      return (score < -72);
   }

   /** implements Comparable. Sorts in descending score order. */
   public int compareTo(Object o) {
      ReusePoint p1 = (ReusePoint) o;
      if (score > p1.score()) return -1;
      if (score < p1.score()) return 1;
      return 0;
   }
   
   

   ExtList children(NonTerminalProgramElement p) {
      ExtList ch = new ExtList();
      for (int k=0; k<p.getChildCount(); k++) ch.add(p.getChildAt(k));
      return ch;
   }

   

   int diffJava(JavaProgramElement x, JavaProgramElement y) {
      StatementCollector c1 = new StatementCollector(templateNode.proof(), x);
      StatementCollector c2 = new StatementCollector(targetGoal.proof(), y);
      c1.start();
      c2.start();
      DiffMyers d = new DiffMyers(c1.result(), c2.result());
      reuseLogger.debug(c1.result());
      reuseLogger.debug(c2.result());
      DiffMyers.change diff = d.diff_2();
      reuseLogger.debug(diff);
      if (diff != null) return diff.diminishingPenalty(); else return 0;
   }
   

   int scoreLogicalFindEqualsMod(Term x, Term y) {
      if (x.depth() == y.depth()) {
         if (x.toString().equals(y.toString()))
            return 10;
      }
      if (x.equalsModRenaming(y)) {
//         System.err.println("1:"+x+"<->"+y+" ["+x.depth());
         return 30; 
      } else return -10;
   }
   
   
   int diffLogical(Term x, Term y) {
      int thisScore;
      Vector xsig = new Vector(20,20);
      Vector ysig = new Vector(20,20);
      Hashtable xDiamonds = new Hashtable(5);
      Hashtable yDiamonds = new Hashtable(5);
      createReuseSignature(x, xsig, xDiamonds);
      createReuseSignature(y, ysig, yDiamonds);
      reuseLogger.debug(xsig);
      reuseLogger.debug(ysig);
      DiffMyers d = new DiffMyers(xsig, ysig);
      DiffMyers.change diff = d.diff_2();
      reuseLogger.debug(diff);
      if (diff != null) thisScore = diff.uniformPenalty(); else thisScore = 0;

      DiffMyers.mapping map = d.getMapping();
      while (map != null) {
         int from = map.from();
         int to = map.to();
         if (xsig.elementAt(from).equals("diamond")) {
            reuseLogger.debug("diamond "+from+"<->"+to);
            Term d1 = (Term) xDiamonds.get(new Integer(from));
            Term d2 = (Term) yDiamonds.get(new Integer(to));
            int diamondScore = diffJava(d1.executableJavaBlock().program(),
                                        d2.executableJavaBlock().program()) / 4;
//            System.err.println(d1);
//            System.err.println(d2);
            reuseLogger.debug("Diamond correspondence penalty "+ diamondScore);
            thisScore += diamondScore;
            
         }
            
         map = map.next();
      }
      thisScore -= Math.abs(xDiamonds.size()-yDiamonds.size())*30;

      return thisScore;
   }
   
   
   int diffPosInTerm(PosInTerm x, PosInTerm y) {
      int thisScore;
     
      DiffMyers d = new DiffMyers(x,y);
      DiffMyers.change diff = d.diff_2();
      reuseLogger.debug(diff);
      if (diff != null) thisScore = diff.uniformPenalty(); else thisScore = 0;
      return thisScore;
   }


   void compareNoFind() {
      reuseLogger.info("*-");
//System.err.println("Comparing terms "+x+"<->"+y);
      int localScore;
      localScore = scoreConnectNoFind(templateNode, targetGoal.node());
//      localScore += scoreConnectSemiseq();
      reuseLogger.info("Connectivity reward "+localScore);
      score += localScore;
      s = s + "Connectivity: "+localScore+"\n";

      localScore = scoreSiblingNr(templateNode, targetGoal.node());
      reuseLogger.info("Sibling order penalty "+localScore);
      score += localScore;
      s = s + "Sibling order penalty: "+localScore+"\n";

      reuseLogger.info("Total score "+score);
      s = s + "-------\n";
      s = s + "Total score: "+score+"\n";
      s = s + "Reuse source: "+ templateNode.serialNr()+"\n";
   }


   
   void compare(Term x, Term y) {
      reuseLogger.info("* "+getApp().rule().name());
//System.err.println("Comparing terms "+x+"<->"+y);
      int localScore;
      JavaBlock jx = x.executableJavaBlock();
      JavaBlock jy = y.executableJavaBlock();
      if (jx.isEmpty() || jy.isEmpty()) {
         
         // not a symbolic execution rule
         localScore = scoreLogicalFindEqualsMod(x,y);
         reuseLogger.info("By equalsModRenaming on find "+localScore);
         score += localScore;
         s = s + "By equalsModRenaming on find "+localScore+"\n";

         localScore = diffLogical(
            templateApp.posInOccurrence().constrainedFormula().formula(),
            targetPos.constrainedFormula().formula());
         reuseLogger.info("By diff on complete formulae "+localScore);
         score += localScore;
         s = s + "By diff on complete formulae "+localScore+"\n";

         localScore = diffPosInTerm(templateApp.posInOccurrence().posInTerm(),
                                    targetPos.posInTerm());
         reuseLogger.info("By diff on PosInTerm "+localScore);
         score += localScore;
         s = s + "By diff on PosInTerm "+localScore+"\n";

      } else { // program similarity
         if (jy.size()>1) {
             localScore = diffJava(jx.program(), jy.program());
             reuseLogger.info("Scored java diff "+localScore);
             score += localScore;
             s = s + "Program similarity "+localScore+"\n";
         } else { // small program -- look at whole formula
             localScore = diffLogical(x, y);
             reuseLogger.info("Scored whole formula (small program) "+localScore);
             score += localScore;
             s = s + "By whole formula (small program) "+localScore+"\n";
         }
      }      

      localScore = scoreConnect(templateNode, targetGoal.node());
//      localScore += scoreConnectSemiseq();
      reuseLogger.info("Connectivity reward "+localScore);
      score += localScore;
      s = s + "Connectivity: "+localScore+"\n";

      localScore = scoreSiblingNr(templateNode, targetGoal.node());
      reuseLogger.info("Sibling order penalty "+localScore);
      score += localScore;
      s = s + "Sibling order penalty: "+localScore+"\n";

      reuseLogger.info("Total score "+score);
      s = s + "-------\n";
      s = s + "Total score: "+score+"\n";
      s = s + "Reuse source: "+ templateNode.serialNr()+"\n";
   }
   
   void compareIf(TacletApp sourceApp, TacletApp targetApp) {
      ListOfIfFormulaInstantiation ifl1 = sourceApp.ifFormulaInstantiations();
      ListOfIfFormulaInstantiation ifl2 = targetApp.ifFormulaInstantiations();
      Term if1;
      ConstrainedFormula iff2;
      Term if2;
      boolean if2inAntec;
      try {
         if1 = ifl1.head().getConstrainedFormula().formula();
         if2inAntec = ((IfFormulaInstSeq)ifl2.head()).inAntec();
         iff2 = ifl2.head().getConstrainedFormula(); 
         if2 = iff2.formula();
      } catch(Exception e) {
         return;
      }
      int i = diffLogical(if1, if2);
      i += scoreLogicalFindEqualsMod(if1,if2);
      score += (i*0.2);
      
      boolean sameFormula;
      PosInOccurrence findPos = targetApp.posInOccurrence();
      
      sameFormula = (findPos.isInAntec() == if2inAntec) &&
          (findPos.constrainedFormula().equals(iff2));
      if (sameFormula) score -= 40;
      
      s = s + "By IF: "+score+"\n";
      
   }
   


   boolean connect = false;
   
   public boolean isConnect() {
      return connect;
   }



   int scoreConnect(Node templateNode, Node targetNode) {
      Node predecSource;
      Node predecTarget;
      try{
         predecSource = templateNode.parent();
         predecTarget = targetNode.parent();
         if (predecTarget.getReuseSource().source()==predecSource) {
            connect = true;
            return 0;
         } else return -70;//-15;
      } catch(NullPointerException npe) {
         return -1; // some ingredient is missing --> neutral score
      }
   }

   int scoreConnectNoFind(Node templateNode, Node targetNode) {
      Node predecSource;
      Node predecTarget;
      try{
         predecSource = templateNode.parent();
         predecTarget = targetNode.parent();
         if (predecTarget.getReuseSource().source()==predecSource) {
            connect = true;
            return 0;
         } else return -100; // kill
      } catch(NullPointerException npe) {
         return -1; // some ingredient is missing --> too bad
      }
   }


   
   int scoreSiblingNr(Node templateNode, Node targetNode) {
       if (templateNode.siblingNr()==targetNode.siblingNr()) return 0;
       else return -1;
   }
   
   
   // not used currently
   int scoreConnectSemiseq() {
      boolean b1 = templateApp.posInOccurrence().isInAntec();
      boolean b2 = targetPos.isInAntec();
      if (b1!=b2) return -10;
      else return 0;
   }
   
   // not used currently
   int twoOpAboveFind() {
      int thisScore = 0;
      reuseLogger.debug(targetPos.posInTerm());
      reuseLogger.debug(templateApp.posInOccurrence().posInTerm());

      // the interface is worth improving...
      if (targetPos.up().subTerm().op() !=
          templateApp.posInOccurrence().up().subTerm().op())
         thisScore = -35;
      if (targetPos.up().up().subTerm().op() !=
          templateApp.posInOccurrence().up().up().subTerm().op())
         thisScore = -35;

      reuseLogger.info("By two operators above "+thisScore);
      return thisScore;
   }
   
   
   
   
   public static void createReuseSignature(Term t, Vector signature,
                                           Hashtable diamondCollector) {
       if (t.op() instanceof IUpdateOperator) {
          createReuseSignature(( (IUpdateOperator)t.op () ).target ( t ),
                               signature, diamondCollector);
          return;
       }
       String termsig = t.op().toString();
//       s = s.substring(s.lastIndexOf(".")+1, s.length());
       
       if ((t.op() instanceof TermSymbol) || (t.op() instanceof AccessOp)) {
          signature.add(t.sort().toString());
          return;
       }
       
       
       signature.add(termsig);
       if ("diamond".equals(termsig)) 
          diamondCollector.put(new Integer(signature.size()-1), t);
//       if (s.equals("Z:int")) return;
       int i;
       for (i=0; i<t.arity(); i++) 
          createReuseSignature(t.sub(i), signature, diamondCollector);
    }

   

   public String scoringInfo() {
      return s;
   }
   
   
   public String toString() {
      return "RP("+score+") "+templateApp.rule().name()+
          ":"+templateNode.serialNr()+"->"+targetGoal.node().serialNr();//" "+sourceTerm();
   }


//***************************************************************


   class StatementCollector extends de.uka.ilkd.key.java.visitor.JavaASTWalker {
   
      Proof proof;
      
   
      StatementCollector(Proof proof, ProgramElement root) {
         super(root);
         this.proof = proof;
      }
   
      Vector result = new Vector(20,20);
      LinkedList executionContext = new LinkedList();
      
      protected void walk(ProgramElement node) {
	  if (node instanceof MethodFrame) {
	      executionContext.addFirst(((MethodFrame)node).getExecutionContext());
          }
          if (node != root()) doAction(node);
	  if (node instanceof NonTerminalProgramElement) {
	      NonTerminalProgramElement nonTerminalNode = 
		  (NonTerminalProgramElement) node;
	      for (int i = 0; i<nonTerminalNode.getChildCount(); i++) {
		  walk(nonTerminalNode.getChildAt(i));
	      }	    
	  }
	  if (node != root()) doLeaveAction(node);
          if (node instanceof MethodFrame) {
              executionContext.removeFirst();
          }
      }


      protected void doAction(ProgramElement node) {
         if (node instanceof StatementBlock) {
//            result.add("{");
            return;
         }
//         if (node instanceof Statement) result.add(node);
         if (node instanceof Statement) {
            final ExecutionContext ec = (ExecutionContext) (executionContext.size() > 0 ? 
                    executionContext.getFirst() : null); 
            result.add(((JavaProgramElement)node).
                    reuseSignature(proof.getServices(), ec));
         }
      }


      protected void doLeaveAction(ProgramElement node) {
//         if (node instanceof StatementBlock) result.add("}");
      }
      
      Vector result() {
         return result;
      }
   }
   

}
