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

package de.uka.ilkd.key.macros;

import java.util.HashSet;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.Strategy;

/**
 * The macro FinishSymbolicExecutionMacro continues automatic rule application
 * until there is no more modality on the sequent.<p>
 * 
 * This is done by implementing a delegation {@link Strategy} which assigns to
 * any rule application infinite costs if there is no modality on the sequent.
 * 
 * @author Mattias Ulbrich
 * @author Dominic Scheurer
 * @see FinishSymbolicExecutionMacro
 */
public class FinishSymbolicExecutionUntilJoinPointMacro extends StrategyProofMacro {

   @Override
   public String getName() {
      return "Finish symbolic execution until join point";
   }

   @Override
   public String getDescription() {
      return "Continue automatic strategy application until a " +
      		"join point is reached or there is no more modality in the sequent.";
   }

   /**
    * Returns true iff there is a modality in the sequent
    * of the given node.
    * 
    * @param node Node to check.
    * @return True iff there is a modality in the sequent of
    *    the given node.
    */
   private static boolean hasModality(Node node) {
      Sequent sequent = node.sequent();
      for (SequentFormula sequentFormula : sequent) {
         if (hasModality(sequentFormula.formula())) {
            return true;
         }
      }

      return false;
   }

   /**
    * Recursive check for existence of modality.
    * 
    * @param term The term to check.
    * @return True iff there is a modality in the sequent of
    *    the given term.
    */
   private static boolean hasModality(Term term) {
      if (term.containsLabel(ParameterlessTermLabel.SELF_COMPOSITION_LABEL)) {
         // ignore self composition terms
         return false;
      }

      if (term.op() instanceof Modality) {
         return true;
      }

      for (Term sub : term.subs()) {
         if (hasModality(sub)) {
            return true;
         }
      }

      return false;
   }

   @Override
   protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
      return new FilterSymbexStrategy(proof.getActiveStrategy());
   }
   
   /**
    * Returns the first Java block in the given term that
    * can be found by recursive search, or the empty block
    * if there is no non-empty Java block in the term.
    * 
    * @param term The term to extract Java blocks for.
    * @return The first Java block in the given term or the
    *    empty block if there is no non-empty Java block.
    */
   private static JavaBlock getJavaBlockRecursive(Term term) {
      if (term.subs().size() == 0 || !term.javaBlock().isEmpty()) {
         return term.javaBlock();
      } else {
         for (Term sub : term.subs()) {
            JavaBlock subJavaBlock = getJavaBlockRecursive(sub);
            if (!subJavaBlock.isEmpty()) {
               return subJavaBlock;
            }
         }
         return JavaBlock.EMPTY_JAVABLOCK;
      }
   }

   /**
    * The Class FilterSymbexStrategy is a special strategy assigning
    * to any rule  infinite costs if the goal has no modality or if
    * a join point is reached.
    */
   private static class FilterSymbexStrategy extends FilterStrategy {
      
      private HashSet<ProgramElement> blockElems = new HashSet<ProgramElement>();

      private static final Name NAME = new Name(
            FilterSymbexStrategy.class.getSimpleName());

      public FilterSymbexStrategy(Strategy delegate) {
         super(delegate);
      }

      @Override
      public Name name() {
         return NAME;
      }

      @Override
      public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
         if (!hasModality(goal.node())) {
            return false;
         }
         
         if (pio != null) {
            JavaBlock theJavaBlock = getJavaBlockRecursive(pio.subTerm());
            
            if (theJavaBlock.program().getFirstElement() instanceof Try) {
               Try theTry = (Try) theJavaBlock.program().getFirstElement();
               
               if (theTry.getBody().getFirstElement() instanceof MethodFrame) {
                  MethodFrame theMethodFrame = (MethodFrame) theTry.getBody().getFirstElement();
                  
                  if (theMethodFrame.getBody().getFirstElement() instanceof If) {
                     if (theMethodFrame.getBody().getChildCount() > 0) {
                        blockElems.add(theMethodFrame.getBody().getChildAt(1));
                     } else {
                        //TODO: Can there come something outside the method frame?
                        //      Or is this case interesting anyway?
                     }
                     
                  } else {
                     if (blockElems.contains((ProgramElement) theMethodFrame.getBody().getFirstElement()))
                        return false;
                  }
               }
            }
         }

         return super.isApprovedApp(app, pio, goal);
      }

   }

}
