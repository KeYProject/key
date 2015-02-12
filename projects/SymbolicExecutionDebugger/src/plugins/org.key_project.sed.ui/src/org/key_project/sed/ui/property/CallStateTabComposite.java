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
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.swt.SWT;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.util.ISEDConstants;


/**
 * This composite provides the content shown in {@link CallStackPropertySection}
 * and in {@code GraphitiCallStackPropertySection}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class CallStateTabComposite extends AbstractNodeTreeTabComposite {
   /**
    * {@inheritDoc}
    */
   @Override
   protected String getGroupName() {
      return "Call state";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected PresentationContext createPresentationContext() {
      return new PresentationContext(ISEDConstants.ID_CALL_STATE); // The current state is IDebugUIConstants.ID_VARIABLE_VIEW.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected int getViewerStyle() {
      return SWT.MULTI | SWT.V_SCROLL | SWT.H_SCROLL | SWT.VIRTUAL | SWT.FULL_SELECTION;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void configurePresentationContext(PresentationContext viewerContext, ISEDDebugNode node) {
      // Nothing to do
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleDoubleClick(DoubleClickEvent event) {
      // Double click is not supported.
   }
}