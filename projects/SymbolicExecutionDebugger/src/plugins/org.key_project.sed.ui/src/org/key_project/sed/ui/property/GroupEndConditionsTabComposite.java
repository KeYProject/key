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

package org.key_project.sed.ui.property;

import org.eclipse.debug.internal.ui.viewers.model.provisional.PresentationContext;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.util.ISEDConstants;

/**
 * This composite provides the content shown in {@link CallStackPropertySection}
 * and in {@code GraphitiCallStackPropertySection}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class GroupEndConditionsTabComposite extends AbstractNodeTreeTabComposite {
   /**
    * {@inheritDoc}
    */
   @Override
   protected String getGroupName() {
      return "Group Ends";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected PresentationContext createPresentationContext() {
      return new PresentationContext(ISEDConstants.ID_GROUP_END_CONDITIONS);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void configurePresentationContext(PresentationContext viewerContext, ISEDDebugNode node) {
      viewerContext.setProperty(ISEDConstants.PRESENTATION_CONTEXT_PROPERTY_INPUT, node);
   }
}