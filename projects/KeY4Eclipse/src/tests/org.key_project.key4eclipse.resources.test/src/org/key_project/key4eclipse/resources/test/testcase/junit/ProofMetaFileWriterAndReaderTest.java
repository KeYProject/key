package org.key_project.key4eclipse.resources.test.testcase.junit;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.junit.Test;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.io.ProofMetaFileAssumption;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.io.ProofMetaFileTypeElement;
import org.key_project.key4eclipse.resources.io.ProofMetaFileWriter;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Tests for {@link ProofMetaFileWriter} and {@link ProofMetaFileReader}.
 * @author Martin Hentschel
 */
public class ProofMetaFileWriterAndReaderTest extends TestCase {
   /**
    * Tests writing and reading
    */
   @Test
   public void testWritingAndReading_Minimal() throws Exception {
      doWritingAndReadingTest("ProofMetaFileWriterAndReaderTest_testWritingAndReading_Minimal", 
                              false, 
                              false, 
                              false, 
                              false, 
                              false);
   }
   
   /**
    * Tests writing and reading
    */
   @Test
   public void testWritingAndReading_Closed() throws Exception {
      doWritingAndReadingTest("ProofMetaFileWriterAndReaderTest_testWritingAndReading_Closed", 
                              true, 
                              false, 
                              false,
                              false,
                              false);
   }
   
   /**
    * Tests writing and reading
    */
   @Test
   public void testWritingAndReading_MarkerMessage() throws Exception {
      doWritingAndReadingTest("ProofMetaFileWriterAndReaderTest_testWritingAndReading_MarkerMessage", 
                              false, 
                              true, 
                              false,
                              false,
                              false);
   }
   
   /**
    * Tests writing and reading
    */
   @Test
   public void testWritingAndReading_Types() throws Exception {
      doWritingAndReadingTest("ProofMetaFileWriterAndReaderTest_testWritingAndReading_Types", 
                              false, 
                              false, 
                              true,
                              false,
                              false);
   }
   
   /**
    * Tests writing and reading
    */
   @Test
   public void testWritingAndReading_Contracts() throws Exception {
      doWritingAndReadingTest("ProofMetaFileWriterAndReaderTest_testWritingAndReading_Contracts", 
                              false, 
                              false, 
                              false,
                              true,
                              false);
   }
   
   /**
    * Tests writing and reading
    */
   @Test
   public void testWritingAndReading_Assumptions() throws Exception {
      doWritingAndReadingTest("ProofMetaFileWriterAndReaderTest_testWritingAndReading_Assumptions", 
                              false, 
                              false, 
                              false,
                              false,
                              true);
   }
   
   /**
    * Tests writing and reading
    */
   @Test
   public void testWritingAndReading_Everything() throws Exception {
      doWritingAndReadingTest("ProofMetaFileWriterAndReaderTest_testWritingAndReading_Everything", 
                              true, 
                              true, 
                              true, 
                              true, 
                              true);
   }
   
   /**
    * Tests writing and reading
    */
   @Test
   public void doWritingAndReadingTest(String projectName,
                                       boolean proofClosed,
                                       boolean withMarkerMessage,
                                       boolean withTypes,
                                       boolean withContracts,
                                       boolean withAssumptions) throws Exception {
      // Create example project
      IProject project = TestUtilsUtil.createProject(projectName);
      IFolder src = TestUtilsUtil.createFolder(project, "src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ProofMetaFileWriterAndReaderTest/src", src);
      IFile javaFile = src.getFile("Main.java");
      IFolder libSpec = TestUtilsUtil.createFolder(project, "libSpec");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ProofMetaFileWriterAndReaderTest/libSpec", libSpec);
      IFolder proofs = TestUtilsUtil.createFolder(project, "proofs");
      IFolder mainProofs = TestUtilsUtil.createFolder(proofs, "Main.java");
      IFolder aProofs = TestUtilsUtil.createFolder(proofs, "A.java");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/ProofMetaFileWriterAndReaderTest/proofs/Main.java", mainProofs);
      IFile proofFile = mainProofs.getFile("Main[Main__magic(A)]_JML_normal_behavior_operation_contract_0.proof");
      IFile metaFile = mainProofs.getFile("Main[Main__magic(A)]_JML_normal_behavior_operation_contract_0.proofmeta");
      IFile anotherProofFile = aProofs.getFile("A[A__contractMagic()]_JML_normal_behavior_operation_contract_0.proof");
      IFile anotherMetaFile = aProofs.getFile("A[A__contractMagic()]_JML_normal_behavior_operation_contract_0.proofmeta");
      // Load existing proof
      KeYEnvironment<CustomUserInterface> env = KeYEnvironment.load(ResourceUtil.getLocation(proofFile), null, null);
      try {
         // Create ProofElement
         Proof proof = env.getLoadedProof();
         assertNotNull(proof);
         ProofElement pe = new ProofElement(javaFile, null, env, proofs, proofFile, metaFile, null, null);
         if (withMarkerMessage) {
            pe.setMarkerMsg("Hello\nWorld\n!");
         }
         pe.setProofClosed(proofClosed);
         if (withTypes || withAssumptions) {
            LinkedHashSet<IProofReference<?>> proofReferences = ProofReferenceUtil.computeProofReferences(proof);
            if (!withTypes || !withAssumptions) {
               Iterator<IProofReference<?>> iter = proofReferences.iterator();
               while (iter.hasNext()) {
                  IProofReference<?> next = iter.next();
                  if (!withTypes && next.getTarget().toString().contains("Main")) {
                     iter.remove();
                  }
                  else if (!withTypes && next.getTarget().toString().contains("A")) {
                     iter.remove();
                  }
                  else if (!withTypes && next.getTarget().toString().contains("pre:") && next.getTarget().toString().contains("<inv>")) {
                     iter.remove();
                  }
                  else if (!withAssumptions && next.getTarget().toString().contains("pre:") && !next.getTarget().toString().contains("<inv>")) {
                     iter.remove();
                  }
               }
            }
            pe.setProofReferences(proofReferences);
         }
         if (withContracts) {
            LinkedList<ProofElement> usedContracts = new LinkedList<ProofElement>();
            usedContracts.add(new ProofElement(javaFile, null, null, proofs, anotherProofFile, anotherMetaFile, null, null));
            pe.setUsedContracts(usedContracts);
         }
         // Write meta file first time
         ProofMetaFileWriter.writeMetaFile(pe);
         assertTrue(metaFile.exists());
         // Read meta file
         ProofMetaFileReader reader = new ProofMetaFileReader(metaFile);
         assertEquals(ResourceUtil.computeContentMD5(proofFile), reader.getProofFileMD5());
         assertEquals(proofClosed, reader.getProofClosed());
         if (withMarkerMessage) {
            assertEquals("Hello\nWorld\n!", reader.getMarkerMessage());
         }
         else {
            assertNull(reader.getMarkerMessage());
         }
         List<ProofMetaFileTypeElement> types = reader.getTypeElements();
         if (withTypes) {
            assertEquals(2, types.size());
            assertEquals("Main", types.get(0).getType());
            assertEquals(0, types.get(0).getSubTypes().size());
            assertEquals("A", types.get(1).getType());
            assertEquals(1, types.get(1).getSubTypes().size());
            assertEquals("B", types.get(1).getSubTypes().get(0));
         }
         else {
            assertEquals(0, types.size());
         }
         LinkedList<IFile> contracts = reader.getUsedContracts();
         if (withContracts) {
            assertEquals(1, contracts.size());
            assertEquals(anotherProofFile, contracts.get(0));
         }
         else {
            assertEquals(0, contracts.size());
         }
         List<ProofMetaFileAssumption> assumptions = reader.getAssumptions();
         if (withAssumptions) {
            assertEquals(1, assumptions.size());
            assertEquals(new ProofMetaFileAssumption("Use Contract", "JML normal_behavior operation contract 0", "identityHashCode(java.lang.Object)", "System"), assumptions.get(0));
         }
         else {
            assertEquals(0, assumptions.size());
         }
      }
      finally {
         env.dispose();
      }
   }
}
