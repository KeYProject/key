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

import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.model.KeYJoin;

import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.util.Triple;

/**
 * This composite provides the content shown in {@link WeakeningPropertySection}
 * and {@link WeakeningGraphitiPropertySection}.
 * @author Martin Hentschel
 */
public class WeakeningComposite extends AbstractTruthValueComposite {
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    * @param layoutListener An optional {@link ILayoutListener} invoked when the shown content has changed.
    */
   public WeakeningComposite(Composite parent, TabbedPropertySheetWidgetFactory factory, ILayoutListener layoutListener) {
      super(parent, factory, layoutListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Node computeNodeToShow(IKeYSENode<?> node, IExecutionNode<?> executionNode) {
      return executionNode.getProofNode().child(0);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Triple<Term, PosInTerm, Term> computeTermToShow(IKeYSENode<?> node,
                                                             IExecutionNode<?> executionNode, 
                                                             Node keyNode) {
      if (node instanceof KeYJoin) {
         Assert.isTrue(0 == keyNode.sequent().antecedent().size(), "Antecedent not empty, CloseAfterJoin implementation has changed.");
         Assert.isTrue(1 == keyNode.sequent().succedent().size(), "Succedent contains not exactly one formula, CloseAfterJoin implementation has changed.");
         Term term = keyNode.sequent().succedent().get(0).formula();
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