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

import org.eclipse.debug.core.Launch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * Provides the basic implementation of {@link AbstractPropertySection}s
 * which shows content of an {@link ISENode}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDebugTargetPropertySection extends AbstractPropertySection {
   /**
    * Returns the {@link ISEDebugTarget} to show.
    * @return The {@link ISEDebugTarget} to show or {@code null} if no one should be shown.
    */
   protected ISEDebugTarget getDebugTarget() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getDebugTarget(object);
   }
   
   /**
    * Converts the given {@link Object} into an {@link ISEDebugTarget} if possible.
    * @param object The given {@link Object}.
    * @return The {@link ISEDebugTarget} or {@code null} if conversion is not possible.
    */
   public static ISEDebugTarget getDebugTarget(Object object) {
      if (object instanceof Launch) {
         IDebugTarget[] targets = ((Launch)object).getDebugTargets();
         return targets != null && targets.length == 1 && targets[0] instanceof ISEDebugTarget ? 
                (ISEDebugTarget)targets[0] : 
                null;
      }
      else {
         return object instanceof ISEDebugTarget ? (ISEDebugTarget)object : null;
      }
   }
}