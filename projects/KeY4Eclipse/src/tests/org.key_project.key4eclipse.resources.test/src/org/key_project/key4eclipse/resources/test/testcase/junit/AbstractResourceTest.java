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

import java.io.File;
import java.io.IOException;

import org.junit.After;
import org.junit.Before;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;

public class AbstractResourceTest extends AbstractSetupTestCase {
   /**
    * <p>
    * If this constant is {@code true} a temporary directory is created with
    * new oracle files. The developer has than to copy the new required files
    * into the plug-in so that they are used during next test execution.
    * </p>
    * <p>
    * <b>Attention: </b> It is strongly required that new test scenarios
    * are verified with the SED application. If everything is fine a new test
    * method can be added to this class and the first test execution can be
    * used to generate the required oracle file. Existing oracle files should
    * only be replaced if the functionality of the Symbolic Execution Debugger
    * has changed so that they are outdated.
    * </p>
    */
   public static final boolean CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY = false;
   
   /**
    * The used temporary oracle directory.
    */
   protected static final File oracleDirectory;

   /**
    * Creates the temporary oracle directory if required.
    */
   static {
      File directory = null;
      try {
         if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            directory = IOUtil.createTempDirectory("ORACLE_DIRECTORY", StringUtil.EMPTY_STRING);
         }
      }
      catch (IOException e) {
      }
      oracleDirectory = directory;
   }

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
   
   /**
    * Prints {@link #oracleDirectory} to the user via {@link System#out}.
    */
   protected static void printOracleDirectory() {
      if (oracleDirectory != null) {
         final String HEADER_LINE = "Oracle Directory is:";
         final String PREFIX = "### ";
         final String SUFFIX = " ###";
         String path = oracleDirectory.toString();
         int length = Math.max(path.length(), HEADER_LINE.length());
         String borderLines = StringUtil.createLine("#", PREFIX.length() + length + SUFFIX.length());
         System.out.println(borderLines);
         System.out.println(PREFIX + HEADER_LINE + StringUtil.createLine(" ", length - HEADER_LINE.length()) + SUFFIX);
         System.out.println(PREFIX + path + StringUtil.createLine(" ", length - path.length()) + SUFFIX);
         System.out.println(borderLines);
      }
   }
}