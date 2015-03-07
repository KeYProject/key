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
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * Provides the basic implementation of {@link AbstractPropertySection}s
 * which shows content of an {@link ISEDDebugNode}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDDebugTargetPropertySection extends AbstractPropertySection {
   /**
    * Returns the {@link ISEDDebugTarget} to show.
    * @return The {@link ISEDDebugTarget} to show or {@code null} if no one should be shown.
    */
   protected ISEDDebugTarget getDebugTarget() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getDebugTarget(object);
   }
   
   /**
    * Converts the given {@link Object} into an {@link ISEDDebugTarget} if possible.
    * @param object The given {@link Object}.
    * @return The {@link ISEDDebugTarget} or {@code null} if conversion is not possible.
    */
   public static ISEDDebugTarget getDebugTarget(Object object) {
      if (object instanceof Launch) {
         IDebugTarget[] targets = ((Launch)object).getDebugTargets();
         return targets != null && targets.length == 1 && targets[0] instanceof ISEDDebugTarget ? 
                (ISEDDebugTarget)targets[0] : 
                null;
      }
      else {
         return object instanceof ISEDDebugTarget ? (ISEDDebugTarget)object : null;
      }
   }
}