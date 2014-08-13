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

package org.key_project.key4eclipse.resources.test.testcase.junit;

import org.junit.After;
import org.junit.Before;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;

public class AbstractResourceTest extends AbstractSetupTestCase {
   private boolean oldAutoBuildEnabled = true;
   
   private StrategyProperties spToRestore;
   
   private int maxStepsToRestore = -1;
   
   @Before
   @Override
   public void setUp() throws Exception {
      super.setUp();
      // Store current settings
      oldAutoBuildEnabled = KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      spToRestore = ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getActiveStrategyProperties();
      maxStepsToRestore = ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
      // Update settings
      StrategyProperties sp = SymbolicExecutionStrategy.getSymbolicExecutionStrategyProperties(false, true, true, false, false);
      ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
      ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(1000);
   }

   @After
   @Override
   public void tearDown() throws Exception {
      super.tearDown();
      // Restore old settings
      if (maxStepsToRestore >= 0) {
         ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxStepsToRestore);
      }
      if (spToRestore != null) {
         ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(spToRestore);
      }
      KeY4EclipseResourcesTestUtil.enableAutoBuild(oldAutoBuildEnabled);
   }
}