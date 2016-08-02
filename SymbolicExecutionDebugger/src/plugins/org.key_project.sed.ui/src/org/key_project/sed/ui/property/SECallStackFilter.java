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

import org.eclipse.debug.core.DebugException;
import org.eclipse.jface.viewers.IFilter;
import org.key_project.sed.core.model.ISENode;
import org.key_project.util.java.ArrayUtil;

/**
 * {@link IFilter} implementation used to define if a {@link CallStackPropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class SECallStackFilter implements IFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Object toTest) {
      try {
         ISENode node = AbstractSENodePropertySection.getDebugNode(toTest);
         return node != null && !ArrayUtil.isEmpty(node.getCallStack());
      }
      catch (DebugException e) {
         return false;
      }
   }
}