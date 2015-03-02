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
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.core.slicing.ISEDSlicer;
import org.key_project.util.java.ArrayUtil;

/**
 * This property tester can be used to make sure that an {@link ISEDVariable} 
 * has some supported {@link ISEDSlicer}.
 * @author Martin Hentschel
 */
public class HasSEDSlicerPropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, 
                       String property, 
                       Object[] args, 
                       Object expectedValue) {
      if (receiver instanceof ISEDVariable) {
         ISEDVariable seedVariable = (ISEDVariable) receiver;
         ISEDDebugTarget target = seedVariable.getDebugTarget();
         if (target != null && seedVariable.getStackFrame() instanceof ISEDDebugNode) {
            ISEDDebugNode seedNode = (ISEDDebugNode) seedVariable.getStackFrame();
            ISEDSlicer[] slicer = target.getSlicer(seedNode, seedVariable);
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