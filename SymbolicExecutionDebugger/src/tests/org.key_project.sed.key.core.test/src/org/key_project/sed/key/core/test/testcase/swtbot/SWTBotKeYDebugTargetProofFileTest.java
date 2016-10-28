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

package org.key_project.sed.key.core.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runners.MethodSorters;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.Activator;

/**
 * Tests for the functionality of a {@link KeYDebugTarget} in which a
 * *.proof file is loaded.
 * @author Martin Hentschel
 */
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class SWTBotKeYDebugTargetProofFileTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Tests the joining of two branches.
    */
   @Test
   public void testJoinTestAfterBranchConditionWithWeakeningGoalNotVerified() throws Exception {
      IKeYDebugTargetProofFileTestExecutor executor = new IKeYDebugTargetProofFileTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IFile file, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, "data/joinTest/oracle/JoinTestAfterBranchConditionWithWeakeningGoalNotVerified.xml", false, false, false);
         }
      };
      doKeYDebugTargetTest("SWTBotKeYDebugTargetProofFileTest_testJoinTestAfterBranchConditionWithWeakeningGoalNotVerified", 
                           Activator.PLUGIN_ID, 
                           "data/joinTest/test", 
                           true, 
                           true, 
                           new IFileSelector() {
                              @Override
                              public IFile getFile(IJavaProject project) throws Exception {
                                 return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path("SWTBotKeYDebugTargetProofFileTest_testJoinTestAfterBranchConditionWithWeakeningGoalNotVerified/src/JoinTestAfterBranchConditionWithWeakeningGoalNotVerified.proof"));
                              }
                           },
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
   
   /**
    * Tests the joining of two branches.
    */
   @Test
   public void testJoinTestAfterBranchConditionWithWeakeningGoal() throws Exception {
      IKeYDebugTargetProofFileTestExecutor executor = new IKeYDebugTargetProofFileTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IFile file, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, "data/joinTest/oracle/JoinTestAfterBranchConditionWithWeakeningGoal.xml", false, false, false);
         }
      };
      doKeYDebugTargetTest("SWTBotKeYDebugTargetProofFileTest_testJoinTestAfterBranchConditionWithWeakeningGoal", 
                           Activator.PLUGIN_ID, 
                           "data/joinTest/test", 
                           true, 
                           true, 
                           new IFileSelector() {
                              @Override
                              public IFile getFile(IJavaProject project) throws Exception {
                                 return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path("SWTBotKeYDebugTargetProofFileTest_testJoinTestAfterBranchConditionWithWeakeningGoal/src/JoinTestAfterBranchConditionWithWeakeningGoal.proof"));
                              }
                           },
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
   
   /**
    * Tests the step over functionality on each branch separately.
    */
   @Test
   public void testBlockContractWithReturnPostconditionNotVerified() throws Exception {
      IKeYDebugTargetProofFileTestExecutor executor = new IKeYDebugTargetProofFileTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IFile file, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, "data/blockContractWithReturnPostconditionNotVerified/oracle/BlockContractWithReturnPostconditionNotVerified.xml", false, true, false);
         }
      };
      doKeYDebugTargetTest("SWTBotKeYDebugTargetProofFileTest_testBlockContractWithReturnPostconditionNotVerified", 
                           Activator.PLUGIN_ID, 
                           "data/blockContractWithReturnPostconditionNotVerified/test", 
                           true, 
                           true, 
                           new IFileSelector() {
                              @Override
                              public IFile getFile(IJavaProject project) throws Exception {
                                 return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path("SWTBotKeYDebugTargetProofFileTest_testBlockContractWithReturnPostconditionNotVerified/src/BlockContractWithReturnPostconditionNotVerified.proof"));
                              }
                           },
                           Boolean.TRUE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
   
   /**
    * Tests the step over functionality on each branch separately.
    */
   @Test
   public void testBlockContractWithReturn() throws Exception {
      IKeYDebugTargetProofFileTestExecutor executor = new IKeYDebugTargetProofFileTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IFile file, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, "data/blockContractWithReturn/oracle/BlockContractWithReturn.xml", false, true, false);
         }
      };
      doKeYDebugTargetTest("SWTBotKeYDebugTargetProofFileTest_testBlockContractWithReturn", 
                           Activator.PLUGIN_ID, 
                           "data/blockContractWithReturn/test", 
                           true, 
                           true, 
                           new IFileSelector() {
                              @Override
                              public IFile getFile(IJavaProject project) throws Exception {
                                 return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path("SWTBotKeYDebugTargetProofFileTest_testBlockContractWithReturn/src/BlockContractWithReturn.proof"));
                              }
                           },
                           Boolean.TRUE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
   
   /**
    * Tests the step over functionality on each branch separately.
    */
   @Test
   public void testBlockContractWithExceptionPostconditionNotVerified() throws Exception {
      IKeYDebugTargetProofFileTestExecutor executor = new IKeYDebugTargetProofFileTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IFile file, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, "data/blockContractWithExceptionPostconditionNotVerified/oracle/BlockContractWithExceptionPostconditionNotVerified.xml", false, true, false);
         }
      };
      doKeYDebugTargetTest("SWTBotKeYDebugTargetProofFileTest_testBlockContractWithExceptionPostconditionNotVerified", 
                           Activator.PLUGIN_ID, 
                           "data/blockContractWithExceptionPostconditionNotVerified/test", 
                           true, 
                           true, 
                           new IFileSelector() {
                              @Override
                              public IFile getFile(IJavaProject project) throws Exception {
                                 return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path("SWTBotKeYDebugTargetProofFileTest_testBlockContractWithExceptionPostconditionNotVerified/src/BlockContractWithExceptionPostconditionNotVerified.proof"));
                              }
                           },
                           Boolean.TRUE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
   
   /**
    * Tests the step over functionality on each branch separately.
    */
   @Test
   public void testBlockContractWithException() throws Exception {
      IKeYDebugTargetProofFileTestExecutor executor = new IKeYDebugTargetProofFileTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IFile file, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, "data/blockContractWithException/oracle/BlockContractWithException.xml", false, true, false);
         }
      };
      doKeYDebugTargetTest("SWTBotKeYDebugTargetProofFileTest_testBlockContractWithException", 
                           Activator.PLUGIN_ID, 
                           "data/blockContractWithException/test", 
                           true, 
                           true, 
                           new IFileSelector() {
                              @Override
                              public IFile getFile(IJavaProject project) throws Exception {
                                 return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path("SWTBotKeYDebugTargetProofFileTest_testBlockContractWithException/src/BlockContractWithException.proof"));
                              }
                           },
                           Boolean.TRUE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
   
   /**
    * Tests the step over functionality on each branch separately.
    */
   @Test
   public void testBlockContractPreconditionNotVerified() throws Exception {
      IKeYDebugTargetProofFileTestExecutor executor = new IKeYDebugTargetProofFileTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IFile file, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, "data/blockContractPreconditionNotVerified/oracle/BlockContractPreconditionNotVerified.xml", false, true, false);
         }
      };
      doKeYDebugTargetTest("SWTBotKeYDebugTargetProofFileTest_testBlockContractPreconditionNotVerified", 
                           Activator.PLUGIN_ID, 
                           "data/blockContractPreconditionNotVerified/test", 
                           true, 
                           true, 
                           new IFileSelector() {
                              @Override
                              public IFile getFile(IJavaProject project) throws Exception {
                                 return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path("SWTBotKeYDebugTargetProofFileTest_testBlockContractPreconditionNotVerified/src/BlockContractPreconditionNotVerified.proof"));
                              }
                           },
                           Boolean.TRUE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
   
   /**
    * Tests the step over functionality on each branch separately.
    */
   @Test
   public void testVerifyMin() throws Exception {
      IKeYDebugTargetProofFileTestExecutor executor = new IKeYDebugTargetProofFileTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IFile file, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, "data/verificationProofFile_VerifyMin/oracle/VerifyMin.xml", true, false, false);
         }
      };
      doKeYDebugTargetTest("SWTBotKeYDebugTargetProofFileTest_testVerifyMin", 
                           Activator.PLUGIN_ID, 
                           "data/verificationProofFile_VerifyMin/test", 
                           true, 
                           true, 
                           new IFileSelector() {
                              @Override
                              public IFile getFile(IJavaProject project) throws Exception {
                                 return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path("SWTBotKeYDebugTargetProofFileTest_testVerifyMin/src/VerifyMin.proof"));
                              }
                           },
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
   
   /**
    * Tests the step over functionality on each branch separately.
    */
   @Test
   public void testMagic42() throws Exception {
      IKeYDebugTargetProofFileTestExecutor executor = new IKeYDebugTargetProofFileTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IFile file, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, "data/magic42/oracle/Magic42ProofFile.xml", true, false, false);
         }
      };
      doKeYDebugTargetTest("SWTBotKeYDebugTargetProofFileTest_testMagic42", 
                           Activator.PLUGIN_ID, 
                           "data/magic42/test", 
                           true, 
                           true, 
                           new IFileSelector() {
                              @Override
                              public IFile getFile(IJavaProject project) throws Exception {
                                 return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path("SWTBotKeYDebugTargetProofFileTest_testMagic42/src/Magic42.proof"));
                              }
                           },
                           Boolean.TRUE, 
                           Boolean.TRUE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
}