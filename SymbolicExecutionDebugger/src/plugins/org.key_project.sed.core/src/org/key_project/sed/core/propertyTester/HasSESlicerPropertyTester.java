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
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEVariable;
import org.key_project.sed.core.slicing.ISESlicer;
import org.key_project.util.java.ArrayUtil;

/**
 * This property tester can be used to make sure that an {@link ISEVariable} 
 * has some supported {@link ISESlicer}.
 * @author Martin Hentschel
 */
public class HasSESlicerPropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, 
                       String property, 
                       Object[] args, 
                       Object expectedValue) {
      if (receiver instanceof ISEVariable) {
         ISEVariable seedVariable = (ISEVariable) receiver;
         ISEDebugTarget target = seedVariable.getDebugTarget();
         if (target != null && seedVariable.getStackFrame() instanceof ISENode) {
            ISENode seedNode = (ISENode) seedVariable.getStackFrame();
            ISESlicer[] slicer = target.getSlicer(seedNode, seedVariable);
            return !ArrayUtil.isEmpty(slicer);
         }
         else {
            return false;
         }
      }
      else {
         return false;
      }
   }
}