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

package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.Iterator;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;
import de.uka.ilkd.key.strategy.termProjection.SVInstantiationProjection;

/**
 * <p>
 * This {@link BinaryFeature} checks if a cut with an equality for
 * an alias check should be done or not.
 * </p>
 * <p>
 * This means the cut is only applied if the cut formula is not an equality
 * or if it is not a negated formula or if the (negated) equality is not contained
 * as top term ({@link SequentFormula}) in the {@link Sequent} ignoring
 * the order of the equality children. 
 * </p>
 * @author Martin Hentschel
 */
public class CutHeapObjectsFeature extends BinaryFeature {
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
      Term cutFormula = SVInstantiationProjection.create(new Name("cutFormula"), false).toTerm(app, pos, goal);
      if (cutFormula != null) {
         if (cutFormula.op() == Junctor.NOT) {
            cutFormula = cutFormula.sub(0);
         }
         if (cutFormula.op() == Equality.EQUALS) {
            Term cutFormulaC0 = cutFormula.sub(0);
            Term cutFormulaC1 = cutFormula.sub(1);
            boolean contains = false;
            Iterator<SequentFormula> iter = goal.sequent().iterator();
            while (!contains && iter.hasNext()) {
               Term formula = iter.next().formula();
               if (formula.op() == Junctor.NOT) {
                  formula = formula.sub(0);
               }
               if (formula.op() == Equality.EQUALS) {
                  // Check equality ignore order of equality sub terms
                  if (cutFormulaC0.equals(formula.sub(0))) {
                     contains = cutFormulaC1.equals(formula.sub(1));
                  }
                  else {
                     contains = cutFormulaC0.equals(formula.sub(1)) &&
                                cutFormulaC1.equals(formula.sub(0));
                  }
               }
            }
            return !contains; // Perform cut only if equality is not already part of the sequent's top formulas
         }
         else {
            return true; // Unknown cut type
         }
      }
      else {
         return false; // Cut without cutFormula is not possible
      }
   }
}