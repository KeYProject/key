/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.ui.property;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.model.KeYLoopBodyTermination;
import org.key_project.sed.key.core.model.KeYLoopInvariant;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Triple;

/**
 * This composite provides the content shown in {@link LoopInvariantPropertySection}
 * and {@link LoopInvariantGraphitiPropertySection}.
 * @author Martin Hentschel
 */
public class LoopInvariantComposite extends AbstractTruthValueComposite {
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    * @param layoutListener An optional {@link ILayoutListener} invoked when the shown content has changed.
    */
   public LoopInvariantComposite(Composite parent, TabbedPropertySheetWidgetFactory factory, ILayoutListener layoutListener) {
      super(parent, factory, layoutListener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Node computeNodeToShow(IKeYSENode<?> node, 
                                    IExecutionNode<?> executionNode) {
      if (node instanceof KeYLoopInvariant) {
         Node invariantNode = super.computeNodeToShow(node, executionNode);
         Node initialNode = invariantNode.child(0);
         assert "Invariant Initially Valid".equals(initialNode.getNodeInfo().getBranchLabel());
         return initialNode;
      }
      else {
         return super.computeNodeToShow(node, executionNode);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Triple<Term, PosInTerm, Term> computeTermToShow(IKeYSENode<?> node, 
                                                             IExecutionNode<?> executionNode, 
                                                             final Node keyNode) {
      if (node instanceof KeYLoopBodyTermination) {
         Term term;
         if (keyNode.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp) {
            OneStepSimplifierRuleApp app = (OneStepSimplifierRuleApp) keyNode.getAppliedRuleApp();
            RuleApp ruleApp = CollectionUtil.search(app.getProtocol(), new IFilter<RuleApp>() {
               @Override
               public boolean select(RuleApp ruleApp) {
                  return SymbolicExecutionUtil.isLoopBodyTermination(keyNode, ruleApp);
               }
            });
            term = ruleApp.posInOccurrence().subTerm();
         }
         else {
            term = executionNode.getModalityPIO().subTerm();
         }
         if (term.op() == Junctor.IMP) {
            term = term.sub(1);
         }
         PosInTerm predicatePosition = findUninterpretedPredicateTerm(term, AbstractOperationPO.getUninterpretedPredicate(executionNode.getProof()));
         Term termWithoutPredicate = removeUninterpretedPredicate(keyNode, term);
         if (!INCLUDE_UPDATES) {
            termWithoutPredicate = TermBuilder.goBelowUpdates(termWithoutPredicate);
         }
         return new Triple<Term, PosInTerm, Term>(termWithoutPredicate, predicatePosition, term);
      }
      else if (node instanceof KeYLoopInvariant) {
         PosInOccurrence pio = executionNode.getModalityPIO();
         Term term;
         if (pio.isInAntec()) {
            int index = executionNode.getProofNode().sequent().antecedent().indexOf(pio.sequentFormula());
            term = keyNode.sequent().antecedent().get(index).formula();
         }
         else {
            int index = executionNode.getProofNode().sequent().succedent().indexOf(pio.sequentFormula());
            term = keyNode.sequent().succedent().get(index).formula();
         }
         if (!INCLUDE_UPDATES) {
            term = TermBuilder.goBelowUpdates(term);
         }
         return new Triple<Term, PosInTerm, Term>(term, null, null);
      }
      else {
         throw new IllegalArgumentException("Unsupported node.");
      }
   }
}