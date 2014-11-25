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
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.sed.key.core.model.KeYMethodContract;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * This composite provides the content shown in {@link PreconditionPropertySection}
 * and {@link PreconditionGraphitiPropertySection}.
 * @author Martin Hentschel
 */
public class PreconditionComposite extends AbstractPredicateComposite {
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public PreconditionComposite(Composite parent, TabbedPropertySheetWidgetFactory factory) {
      super(parent, factory);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Node computeNodeToShow(IKeYSEDDebugNode<?> node, 
                                    IExecutionNode<?> executionNode) {
      if (node instanceof KeYMethodContract) {
         Node invariantNode = super.computeNodeToShow(node, executionNode);
         Node preNode = invariantNode.child(2);
         assert preNode.getNodeInfo().getBranchLabel().startsWith("Pre");
         return preNode;
      }
      else {
         return super.computeNodeToShow(node, executionNode);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Term computeTermToShow(IKeYSEDDebugNode<?> node,
                                    IExecutionNode<?> executionNode, 
                                    Node keyNode) {
      if (node instanceof KeYMethodContract) {
         PosInOccurrence pio = executionNode.getModalityPIO();
         Term term;
         if (pio.isInAntec()) {
            int index = executionNode.getProofNode().sequent().antecedent().indexOf(pio.constrainedFormula());
            term = keyNode.sequent().antecedent().get(index).formula();
         }
         else {
            int index = executionNode.getProofNode().sequent().succedent().indexOf(pio.constrainedFormula());
            term = keyNode.sequent().succedent().get(index).formula();
         }
         term = TermBuilder.goBelowUpdates(term);
         return term;
      }
      else {
         throw new IllegalArgumentException("Unsupported node.");
      }
   }
}