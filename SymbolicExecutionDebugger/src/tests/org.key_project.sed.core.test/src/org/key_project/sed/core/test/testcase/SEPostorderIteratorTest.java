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
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.util.ISEIterator;
import org.key_project.sed.core.util.SEPostorderIterator;

/**
 * Contains tests for {@link SEPostorderIterator}.
 * @author Martin Hentschel
 */
public class SEPostorderIteratorTest extends AbstractSEIteratorTest {
   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEIterator createIterator(ISEDebugElement start) throws DebugException {
      return new SEPostorderIterator(start);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void assertExpectedNodes(ISEIterator iter, 
                                      ExpectedNode root,
                                      boolean iterateOverSubtree) throws DebugException {
      // Test children
      ExpectedNode[] expectedChildren = root.getExpectedChildren();
      if (expectedChildren != null) {
         for (ExpectedNode child : expectedChildren) {
            assertExpectedNodes(iter, child, true);
         }
      }
      // Test current node
      assertNotNull(root);
      assertTrue(iter.hasNext());
      ISEDebugElement next = iter.next();
      assertNotNull(next);
      if (next instanceof ISEDebugTarget) {
         assertEquals(root.getExpectedName(), ((ISEDebugTarget)next).getName());
      }
      else if (next instanceof ISENode) {
         assertEquals(root.getExpectedName(), ((ISENode)next).getName());
      }
      else {
         fail("Unknown element \"" + next + "\".");
      }
      if (iterateOverSubtree) {
         assertTarget(next, root);
      }
   }
}