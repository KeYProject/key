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
import org.eclipse.jface.viewers.IFilter;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDGroupable;
import org.key_project.util.java.ArrayUtil;

/**
 * {@link IFilter} implementation used to check if
 * {@link ISEDGroupable#getGroupEndConditions()} is not empty.
 * @author Martin Hentschel
 */
public class GraphitiConstraintsTreeFilter extends GraphitiReadonlyDebugNodeTreeFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean accept(PictogramElement pe, AbstractGraphitiDebugNodePropertySection section) {
      try {
         if (super.accept(pe, section)) {
            ISEDDebugNode node = section.getDebugNode(pe);
            return node != null && !ArrayUtil.isEmpty(node.getConstraints());
         }
         else {
            return false;
         }
      }
      catch (DebugException e) {
         return false;
      }
   }
}