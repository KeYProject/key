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

import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;


public class ReuseUpdateSimplificationRule {

   private List reusePoints;
   private KeYMediator medi;
   private Constraint userC;

   public ReuseUpdateSimplificationRule(KeYMediator medi, List reusePoints) {
       this.medi = medi;
       this.reusePoints = reusePoints;
       userC = medi.getUserConstraint().getConstraint();
   }


   public void applicableWhere(ReusePoint blank) {
      Goal g = blank.target();
      RuleApp templateApp = blank.getApp();

      IteratorOfConstrainedFormula formIter;
      
      final PosInOccurrence pio = templateApp.posInOccurrence();
      
      if (pio==null) {
	 final RuleApp tentativeApp = 
             isApplicable((BuiltInRule)templateApp.rule(),
                     blank.target(), null);
	 if (tentativeApp != null) {
             ReusePoint p = blank.initializeNoFind(tentativeApp, medi);
             if ((p != null)){ // RuleApp can be transferred // && goodEnough!
        	reusePoints.add(p);
             }
	 }
	 return;
      }
      else
      if (pio.isInAntec()) {
         formIter = g.sequent().antecedent().iterator();
      } else {
         formIter = g.sequent().succedent().iterator();
      }

      final boolean inAntec = pio.isInAntec(); 
      
      // but only if pos taclet
      while (formIter.hasNext()) {
         ConstrainedFormula cfma = formIter.next();
         PosInOccurrence start = 
            new PosInOccurrence(cfma, PosInTerm.TOP_LEVEL, inAntec);
         recMatch(start, cfma.formula(), (BuiltInRule)templateApp.rule(), blank);
      }
   }

   private void recMatch(PosInOccurrence pos, Term t, BuiltInRule rule,
                         ReusePoint blank) {
      
      RuleApp tentativeApp = isApplicable(rule, blank.target(), pos);
      if (tentativeApp != null) {
          ReusePoint p = blank.initialize(pos, tentativeApp, medi);
          if ((p != null)){ // RuleApp can be transferred // && goodEnough!
             reusePoints.add(p);
          }
      }
      // Succ- and Antec- are only applicable at top-level of formula
      // if (!(rule instanceof RewriteTaclet)) return;
      // does it make sense to do extra update simp on subformulas?
      // let's suppose that it's not 
      /*
      int i;
      for (i=0; i<t.arity(); i++) {
         recMatch(pos.down(i), t.sub(i), rule, blank);
      }
      */
   }


   private RuleApp isApplicable(BuiltInRule rule, Goal g, PosInOccurrence pos) {       
       if (!rule.isApplicable(g, pos, userC)) { 
           return null;
       } else {
           final RuleApp app = new BuiltInRuleApp(rule, pos, userC);
           return app;
       }
   }

}
