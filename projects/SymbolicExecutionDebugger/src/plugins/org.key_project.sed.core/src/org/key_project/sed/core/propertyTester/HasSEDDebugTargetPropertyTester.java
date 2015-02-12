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

package org.key_project.sed.core.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

/**
 * This property tester can be used to make sure that an {@link ILaunch} 
 * has at least one {@link ISEDDebugTarget}.
 * @author Martin Hentschel
 */
public class HasSEDDebugTargetPropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, 
                       String property, 
                       Object[] args, 
                       Object expectedValue) {
      if (receiver instanceof ILaunch) {
         ILaunch launch = (ILaunch)receiver;
         return ArrayUtil.search(launch.getDebugTargets(), new IFilter<IDebugTarget>() {
            @Override
            public boolean select(IDebugTarget element) {
               return element instanceof ISEDDebugTarget;
            }
         }) != null;
      }
      else {
         return false;
      }
   }
}