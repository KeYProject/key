package org.key_project.key4eclipse.resources.test.testcase.junit;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Path;
import org.junit.Test;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;

/**
 * Tests to ensure that the auto mode is started after a specification was added.
 * @author Martin Hentschel
 */
public class AutoModeStartingSpecificationTest extends AbstractResourceTest {
   /**
    * Tests that the auto mode is started after adding a block contract.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testMethodContractAdded() throws Exception {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoModeStartingSpecificationTest_testMethodContractAdded", true, false, false, false, 1, false, false, false);
      try {
         doSourceFileChangeTest(project,
                                "data/AddMethodContractTest/before/MethodContractTest.proof",
                                "data/AddMethodContractTest/before/MethodContractTest.java",
                                false,
                                false,
                                "data/AddMethodContractTest/after/MethodContractTest.java",
                                true,
                                "MethodContractTest.java/MethodContractTest[MethodContractTest__setValueToOne()]_JML_normal_behavior_operation_contract_0.proof");
      }
      finally {
         project.close(null);
      }
   }
   
   /**
    * Tests that the auto mode is started after adding a block contract.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testBlockContractAdded() throws Exception {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoModeStartingSpecificationTest_testBlockContractAdded", true, false, false, false, 1, false, false, false);
      try {
         doSourceFileChangeTest(project,
                                "data/AddBlockContractTest/before/BlockContractTest.proof",
                                "data/AddBlockContractTest/before/BlockContractTest.java",
                                false,
                                false,
                                "data/AddBlockContractTest/after/BlockContractTest.java",
                                true,
                                "BlockContractTest.java/BlockContractTest[BlockContractTest__setValueToOne()]_JML_normal_behavior_operation_contract_0.proof");
      }
      finally {
         project.close(null);
      }
   }
   
   /**
    * Tests that the auto mode is started after adding a loop invariant.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testLoopInvariantAdded() throws Exception {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("AutoModeStartingSpecificationTest_testLoopInvariantAdded", true, false, false, false, 1, false, false, false);
      try {
         doSourceFileChangeTest(project,
                                "data/AddLoopInvariantTest/before/LoopInvariantExample.proof",
                                "data/AddLoopInvariantTest/before/LoopInvariantExample.java",
                                false,
                                true,
                                "data/AddLoopInvariantTest/after/LoopInvariantExample.java",
                                true,
                                "LoopInvariantExample.java/LoopInvariantExample[LoopInvariantExample__setAllToOne()]_JML_normal_behavior_operation_contract_0.proof");
      }
      finally {
         project.close(null);
      }
   }
   
   /**
    * Performs the test steps in which an initial file is replaced by a new one.
    * @param project The {@link IProject} to work with.
    * @param beforeProofFile The path in the bundle to the before source file.
    * @param beforeSourcePath The path in the bundle to the before proof file.
    * @param expectedBeforeProofClosed The expected before closed state.
    * @param startAutoModeAfterBefore Start auto mode after the before phase?
    * @param afterSourcePath The path in the bundle to the after source file.
    * @param expectedAfterProofClosed The expected after closed state.
    * @param proofPathInProofFolder The path in the proof folder to the proof file to test.
    * @throws Exception Occurred Exception.
    */
   protected void doSourceFileChangeTest(IProject project, 
                                         String beforeProofFile,
                                         String beforeSourcePath,
                                         boolean expectedBeforeProofClosed,
                                         boolean startAutoModeAfterBefore,
                                         String afterSourcePath,
                                         boolean expectedAfterProofClosed,
                                         String proofPathInProofFolder) throws Exception {
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      assertTrue(proofFolder.exists());
      IFile proofFile = proofFolder.getFile(new Path(proofPathInProofFolder));
      ResourceUtil.ensureExists(proofFile.getParent());
      assertFalse(proofFile.exists());
      // Add and test before file
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, beforeSourcePath, project.getFolder(JDTUtil.getSourceFolderName()), true);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, beforeProofFile, proofFile);
      if (startAutoModeAfterBefore) {
         KeY4EclipseResourcesTestUtil.build(project);
      }
      assertTrue(proofFile.exists());
      assertProofClosedStatus(proofFile, expectedBeforeProofClosed);
      // Add and test after file
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, afterSourcePath, project.getFolder(JDTUtil.getSourceFolderName()), true);
      KeY4EclipseResourcesTestUtil.build(project);
      assertTrue(proofFile.exists());
      assertProofClosedStatus(proofFile, expectedAfterProofClosed);
   }

   /**
    * Checks if the given proof file has the expected closed state.
    * @param proofFile The proof file.
    * @param expectedClosed The expected close state.
    * @throws Exception Occurred Exception.
    */
   protected void assertProofClosedStatus(IFile proofFile, boolean expectedClosed) throws Exception {
      KeYEnvironment<?> env = KeYEnvironment.load(ResourceUtil.getLocation(proofFile));
      Proof proof = null;
      try {
         proof = env.getLoadedProof();
         assertNotNull(proof);
         assertEquals(expectedClosed, proof.closed());
      }
      finally {
         if (proof != null) {
            proof.dispose();
         }
         if (env != null) {
            env.dispose();
         }
      }
   }
}
