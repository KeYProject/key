/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.sed.key.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.util.java.ArrayUtil;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * This property tester can be used to make sure that an {@link ILaunch} 
 * contains exactly one {@link KeYDebugTarget} and that {@link IDebugElement}s
 * are contained in a {@link KeYDebugTarget}, 
 * @author Martin Hentschel
 */
public class KeYDebugTargetPropertyTester extends PropertyTester {
   /**
    * Argument to verify also that the {@link KeYDebugTarget} is not terminated.
    */
   public static final String NOT_DISPOSED_ARGUMENT = "notTerminated";

   /**
    * Argument to verify also that the proof is not shown in KeY's {@link MainWindow}.
    */
   public static final String NOT_KEY_MAIN_WINDOW = "notKeYMainWindow";

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, 
                       String property, 
                       Object[] args, 
                       Object expectedValue) {
      KeYDebugTarget target = null;
      if (receiver instanceof ILaunch) {
         ILaunch launch = (ILaunch)receiver;
         if (launch.getDebugTargets() != null && 
             launch.getDebugTargets().length == 1 && 
             launch.getDebugTargets()[0] instanceof KeYDebugTarget) {
            target = (KeYDebugTarget)launch.getDebugTargets()[0];
         }
      }
      else if (receiver instanceof IDebugElement)  {
         IDebugElement element = (IDebugElement)receiver;
         if (element.getDebugTarget() instanceof KeYDebugTarget) {
            target = (KeYDebugTarget)element.getDebugTarget();
         }
      }
      boolean result = target != null;
      if (result && ArrayUtil.contains(args, NOT_DISPOSED_ARGUMENT)) {
         result = !target.isTerminated();
      }
      if (result && ArrayUtil.contains(args, NOT_KEY_MAIN_WINDOW)) {
         result = !target.getLaunchSettings().isShowKeYMainWindow();
      }
      return result;
   }
}