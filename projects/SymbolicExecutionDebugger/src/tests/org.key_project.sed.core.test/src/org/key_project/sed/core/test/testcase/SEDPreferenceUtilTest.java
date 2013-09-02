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

package org.key_project.sed.core.test.testcase;

import junit.framework.TestCase;

import org.eclipse.jface.preference.IPreferenceStore;
import org.junit.Test;
import org.key_project.sed.core.test.testcase.swtbot.SWTBotDebugViewHierarchyTest;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;

/**
 * Tests for {@link SEDPreferenceUtil}.
 * @author Martin Hentschel
 */
public class SEDPreferenceUtilTest extends AbstractSetupTestCase {
   /**
    * Tests the preference toggle functionality of
    * {@link SEDPreferenceUtil#toggleShowCompactExecutionTreePreference()}.
    * That all trees in the user interface are updated is tested in
    * {@link SWTBotDebugViewHierarchyTest#testSwitchingBetweenCompactAndNormalHierarchy()}.
    */
   @Test
   public void testToggleShowCompactExecutionTreePreference() {
      boolean currentValue = SEDPreferenceUtil.isShowCompactExecutionTree();
      boolean defaultValue = SEDPreferenceUtil.isDefaultShowCompactExecutionTree();
      try {
         // Test initial values
         assertTrue(SEDPreferenceUtil.isShowCompactExecutionTree());
         assertTrue(SEDPreferenceUtil.isDefaultShowCompactExecutionTree());
         // Toggle to false
         SEDPreferenceUtil.toggleShowCompactExecutionTreePreference();
         assertFalse(SEDPreferenceUtil.isShowCompactExecutionTree());
         assertTrue(SEDPreferenceUtil.isDefaultShowCompactExecutionTree());
         // Toggle to true
         SEDPreferenceUtil.toggleShowCompactExecutionTreePreference();
         assertTrue(SEDPreferenceUtil.isShowCompactExecutionTree());
         assertTrue(SEDPreferenceUtil.isDefaultShowCompactExecutionTree());
      }
      finally {
         SEDPreferenceUtil.setShowCompactExecutionTree(currentValue);
         SEDPreferenceUtil.setDefaultShowCompactExecutionTree(defaultValue);
      }
   }
   
   /**
    * Tests {@link SEDPreferenceUtil#isShowCompactExecutionTree()},
    * {@link SEDPreferenceUtil#isDefaultShowCompactExecutionTree()},
    * {@link SEDPreferenceUtil#setShowCompactExecutionTree(boolean)} and
    * {@link SEDPreferenceUtil#setDefaultShowCompactExecutionTree(boolean)}
    */
   @Test
   public void testPreferenceShowCompactSymbolicExecutionTree() {
      boolean currentValue = SEDPreferenceUtil.isShowCompactExecutionTree();
      boolean defaultValue = SEDPreferenceUtil.isDefaultShowCompactExecutionTree();
      try {
         // Test initial values
         assertTrue(SEDPreferenceUtil.isShowCompactExecutionTree());
         assertTrue(SEDPreferenceUtil.isDefaultShowCompactExecutionTree());
         // Change current value to false
         SEDPreferenceUtil.setShowCompactExecutionTree(false);
         assertFalse(SEDPreferenceUtil.isShowCompactExecutionTree());
         assertTrue(SEDPreferenceUtil.isDefaultShowCompactExecutionTree());
         // Set default value to false
         SEDPreferenceUtil.setDefaultShowCompactExecutionTree(false);
         assertFalse(SEDPreferenceUtil.isShowCompactExecutionTree());
         assertFalse(SEDPreferenceUtil.isDefaultShowCompactExecutionTree());
         // Change current value to true
         SEDPreferenceUtil.setShowCompactExecutionTree(true);
         assertTrue(SEDPreferenceUtil.isShowCompactExecutionTree());
         assertFalse(SEDPreferenceUtil.isDefaultShowCompactExecutionTree());
         // Set default value to true
         SEDPreferenceUtil.setDefaultShowCompactExecutionTree(true);
         assertTrue(SEDPreferenceUtil.isShowCompactExecutionTree());
         assertTrue(SEDPreferenceUtil.isDefaultShowCompactExecutionTree());
      }
      finally {
         SEDPreferenceUtil.setShowCompactExecutionTree(currentValue);
         SEDPreferenceUtil.setDefaultShowCompactExecutionTree(defaultValue);
      }
   }
   
   /**
    * Tests {@link SEDPreferenceUtil#getStore()}
    */
   @Test
   public void testGetStore() {
      IPreferenceStore store = SEDPreferenceUtil.getStore();
      assertNotNull(store);
   }
}