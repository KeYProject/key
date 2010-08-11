// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.reuse;

import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.*;


public class ReuseFindTaclet {

   private List reusePoints;
   private KeYMediator medi;
   private Services services;
   private Constraint userC;
   private InitConfig iconfig;

   public ReuseFindTaclet(KeYMediator medi, List reusePoints) {
       this.medi = medi;
       this.reusePoints = reusePoints;
       services = medi.getServices();
       userC = medi.getUserConstraint().getConstraint();
       iconfig = medi.getProof().env().getInitConfig();
   }


   public void applicableWhere(ReusePoint blank) {
      Goal g = blank.target();
      RuleApp templateApp = blank.getApp();

      final boolean inAntec = templateApp.posInOccurrence().isInAntec();
      
      final Iterator<ConstrainedFormula> formIter;

      if (inAntec) {
         formIter = g.sequent().antecedent().iterator();         
      } else {
         formIter = g.sequent().succedent().iterator();         
      }
         
      Rule rule = iconfig.lookupActiveTaclet(templateApp.rule().name());
      if (rule==null) { // goal local rule
          rule = g.indexOfTaclets().lookup(templateApp.rule().name()).rule();
          blank.setGoalLocal(true);
      }

      // but only if pos taclet
      while (formIter.hasNext()) {
         final ConstrainedFormula cfma = formIter.next();
         final PosInOccurrence start = 
            new PosInOccurrence(cfma, PosInTerm.TOP_LEVEL, inAntec);
         recMatch(start, cfma.formula(), rule, blank);
      }
   }

   private void recMatch(PosInOccurrence pos, Term t, Rule rule,
                         ReusePoint blank) {
      
      final TacletApp tentativeApp = isApplicable(rule, pos, t);
      if (tentativeApp != null) {
          checkIfInstsAndRecord(blank, pos, tentativeApp);
      }
      // Succ- and Antec- are only applicable at top-level of formula
      if (!(rule instanceof RewriteTaclet)) return;
      for (int i = 0, arity = t.arity(); i<arity; i++) {
         recMatch(pos.down(i), t.sub(i), rule, blank);
      }
   }

   private void checkIfInstsAndRecord(ReusePoint blank, PosInOccurrence pos, 
                                      TacletApp tentativeApp) {

         final ImmutableList<TacletApp> ifCandidates;
         if (!tentativeApp.ifInstsComplete()) {
             ifCandidates = tentativeApp.findIfFormulaInstantiations(
 	        blank.target().sequent(), services, userC);
         } else {
             ifCandidates = ImmutableSLList.<TacletApp>nil().prepend(tentativeApp);
         }

       for (TacletApp ifCandidate : ifCandidates) {
           final ReusePoint p = blank.initialize(pos, ifCandidate, medi);
           if ((p != null)) { // RuleApp can be transferred // && goodEnough!
               reusePoints.add(p);
           }
       }
   }


   private TacletApp isApplicable(Rule rule, PosInOccurrence pos, Term t) {
      if (rule instanceof FindTaclet) {
         //this is copied from TermTacletAppIndex :-/
	 Constraint c = pos.constrainedFormula().constraint();
	 if ( pos.termBelowMetavariable() != null ) {
	     c = c.unify( 
                pos.constrainedFormula().formula().subAt(pos.posInTerm()),
		pos.termBelowMetavariable(), services);
	     if (!c.isSatisfiable()) return null;
	 }

         NoPosTacletApp app = NoPosTacletApp.createNoPosTacletApp(
            (FindTaclet)rule);
         app = app.matchFind(pos, c, services, userC, t);
         if (app==null) return null;
         
         return app.setPosInOccurrence(pos);
         
      } else 
         throw new RuntimeException("Not a FindTaclet: Re-Use Failed "+rule);

   }

}
