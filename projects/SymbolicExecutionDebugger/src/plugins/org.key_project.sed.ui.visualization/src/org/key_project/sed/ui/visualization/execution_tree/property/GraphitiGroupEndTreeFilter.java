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

package org.key_project.sed.ui.visualization.execution_tree.property;

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.platform.AbstractPropertySectionFilter;
import org.eclipse.jface.viewers.IFilter;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.sed.core.model.ISEDGroupable;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.property.ISEDDebugNodeTabContent;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * {@link IFilter} implementation used to check if
 * {@link ISEDGroupable#getGroupEndConditions()} is not empty.
 * @author Martin Hentschel
 */
public class GraphitiGroupEndTreeFilter extends AbstractPropertySectionFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean accept(PictogramElement pe) {
      IWorkbenchPart part = WorkbenchUtil.getActivePart();
      if (part != null) {
         AbstractGraphitiDebugNodePropertySection section = new AbstractGraphitiDebugNodePropertySection() {
            @Override
            protected ISEDDebugNodeTabContent createContent() {
               return null; // Is never used.
            }
         };
         section.setInput(part, null);
         return accept(pe, section);
      }
      else {
         return false;
      }
   }
   
   /**
    * Checks if the given {@link PictogramElement} should be accept in the given {@link AbstractGraphitiDebugNodePropertySection}.
    * @param pe The {@link PictogramElement} to check.
    * @param section The {@link AbstractGraphitiDebugNodePropertySection} to check.
    * @return {@code true} accept, {@code false} do not accept.
    */
   protected boolean accept(PictogramElement pe, AbstractGraphitiDebugNodePropertySection section) {
      try {
         ISEDDebugNode node = section.getDebugNode(pe);
         return node instanceof ISEDGroupable && !ArrayUtil.isEmpty(((ISEDGroupable) node).getGroupEndConditions());
      }
      catch (DebugException e) {
         return false;
      }
   }
}