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
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.util.LogUtil;

/**
 * This property tester can be used to make sure that an {@link IStackFrame} 
 * has some {@link IVariable}s tested via {@link IStackFrame#hasVariables()}. 
 * @author Martin Hentschel
 */
public class StackFrameHasVariablesPropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, 
                       String property, 
                       Object[] args, 
                       Object expectedValue) {
      try {
         if (receiver instanceof IStackFrame) {
            return ((IStackFrame)receiver).hasVariables();
         }
         else {
            return false;
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }
}