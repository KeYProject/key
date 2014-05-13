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

package org.key_project.sed.core.test.testcase;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.SEDPreorderIterator;

/**
 * Contains tests for {@link SEDPreorderIterator}.
 * @author Martin Hentschel
 */
public class SEDPreorderIteratorTest extends AbstractSEDIteratorTest {
   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDIterator createIterator(ISEDDebugElement start) throws DebugException {
      return new SEDPreorderIterator(start);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void assertExpectedNodes(ISEDIterator iter, 
                                      ExpectedNode root,
                                      boolean iterateOverSubtree) throws DebugException {
      // Test current node
      assertNotNull(root);
      assertTrue(iter.hasNext());
      ISEDDebugElement next = iter.next();
      assertNotNull(next);
      if (next instanceof ISEDDebugTarget) {
         assertEquals(root.getExpectedName(), ((ISEDDebugTarget)next).getName());
      }
      else if (next instanceof ISEDDebugNode) {
         assertEquals(root.getExpectedName(), ((ISEDDebugNode)next).getName());
      }
      else {
         fail("Unknown element \"" + next + "\".");
      }
      if (iterateOverSubtree) {
         assertTarget(next, root);
      }
      // Test children
      ExpectedNode[] expectedChildren = root.getExpectedChildren();
      if (expectedChildren != null) {
         for (ExpectedNode child : expectedChildren) {
            assertExpectedNodes(iter, child, true);
         }
      }
   }
}