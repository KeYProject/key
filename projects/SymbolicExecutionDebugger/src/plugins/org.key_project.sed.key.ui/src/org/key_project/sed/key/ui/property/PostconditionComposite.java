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

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * This composite provides the content shown in {@link PostconditionPropertySection}
 * and {@link PostconditionGraphitiPropertySection}.
 * @author Martin Hentschel
 */
public class PostconditionComposite extends AbstractPredicateComposite {
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public PostconditionComposite(Composite parent, TabbedPropertySheetWidgetFactory factory) {
      super(parent, factory);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Term computeTermToShow(IKeYSEDDebugNode<?> node,
                                    IExecutionNode<?> executionNode, 
                                    Node keyNode) {
      Term term = keyNode.getAppliedRuleApp().posInOccurrence().subTerm();
      if (term.op() instanceof Modality) {
         term = term.sub(0);
      }
      term = removeUninterpretedPredicate(keyNode, term);
      return term;
   }
}