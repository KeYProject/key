package org.key_project.key4eclipse.resources.test.testcase.junit;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.junit.Test;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.io.ProofMetaFileAssumption;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.io.ProofMetaFileWriter;
import org.key_project.key4eclipse.resources.io.ProofMetaPerTypeReferences;
import org.key_project.key4eclipse.resources.io.ProofMetaReferences;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.Contract;

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
                              false,
                              false);
   }
   
   /**
    * Tests writing and reading
    */
   @Test
   public void testWritingAndReading_Outdated() throws Exception {
      doWritingAndReadingTest("ProofMetaFileWriterAndReaderTest_testWritingAndReading_Outdated", 
                              false,
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
                              true, 
                              true);
   }
   
   /**
    * Tests writing and reading
    */
   @Test
   public void doWritingAndReadingTest(String projectName,
                                       boolean proofClosed,
                                       boolean proofOutdated,
                                       boolean withMarkerMessage,
                                       boolean withProofMetaReferences,
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
      // Load existing proof
      KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(ResourceUtil.getLocation(proofFile), null, null, null);
      try {
         // Create ProofElement
         Proof proof = env.getLoadedProof();
         assertNotNull(proof);
         Contract c = env.getSpecificationRepository().getContractByName("Main[Main::magic(A)].JML normal_behavior operation contract.0");
         ProofElement pe = new ProofElement(javaFile, null, env, proofs, proofFile, metaFile, null, null, c);
         if (withMarkerMessage) {
            pe.setMarkerMsg("Hello\nWorld\n!");
         }
         pe.setProofClosed(proofClosed);
         pe.setOutdated(proofOutdated);
         if (withProofMetaReferences || withAssumptions) {
            LinkedHashSet<IProofReference<?>> proofReferences = ProofReferenceUtil.computeProofReferences(proof);
            if (!withProofMetaReferences || !withAssumptions) {
               Iterator<IProofReference<?>> iter = proofReferences.iterator();
               while (iter.hasNext()) {
                  IProofReference<?> next = iter.next();
                  if (!withProofMetaReferences && next.getTarget().toString().contains("Main")) {
                     iter.remove();
                  }
                  else if (!withProofMetaReferences && next.getTarget().toString().contains("A")) {
                     iter.remove();
                  }
                  else if (!withProofMetaReferences && next.getTarget().toString().contains("pre:") && next.getTarget().toString().contains("<inv>")) {
                     iter.remove();
                  }
                  else if (!withAssumptions && next.getTarget().toString().contains("pre:") && !next.getTarget().toString().contains("<inv>")) {
                     iter.remove();
                  }
               }
            }
            Set<IProofReference<?>> filteredProofReferences = new LinkedHashSet<IProofReference<?>>();
            Set<IProofReference<?>> assumptions = new LinkedHashSet<IProofReference<?>>();
            KeYResourcesUtil.filterProofReferences(proofReferences, filteredProofReferences, assumptions);
            pe.setAssumptions(KeYResourcesUtil.computeProofMetaFileAssumtionList(pe.getKeYEnvironment().getServices(), assumptions));
            if(withProofMetaReferences){
               pe.setProofMetaReferences(new ProofMetaReferences(pe, filteredProofReferences));
            }
         }
         if (withContracts) {
            LinkedList<IFile> usedContracts = new LinkedList<IFile>();
            usedContracts.add(anotherProofFile);
            pe.setUsedContracts(usedContracts);
         }
         // Write meta file first time
         ProofMetaFileWriter.writeMetaFile(pe);
         assertTrue(metaFile.exists());
         // Read meta file
         ProofMetaFileReader reader = new ProofMetaFileReader(metaFile);
         assertEquals(ResourceUtil.computeContentMD5(proofFile), reader.getProofFileMD5());
         assertEquals(proofClosed, reader.getProofClosed());
         assertEquals(proofOutdated, reader.getProofOutdated());
         if (withMarkerMessage) {
            assertEquals("Hello\nWorld\n!", reader.getMarkerMessage());
         }
         else {
            assertNull(reader.getMarkerMessage());
         }
         ProofMetaReferences refs = reader.getReferences();
         if (withProofMetaReferences) {
            assertEquals(pe.getContract().toString(), refs.getContract());
            assertEquals(1, refs.getCallMethods().size());
            Map<String, ProofMetaPerTypeReferences> ptRefs = refs.getPerTypeReferences();
            assertEquals(2, ptRefs.size());
            ProofMetaPerTypeReferences typeARefs = ptRefs.get("A");
            assertEquals(0, typeARefs.getAxioms().size());
            assertEquals(0, typeARefs.getInvariants().size());
            assertEquals(0, typeARefs.getAccesses().size());
            assertEquals(1, typeARefs.getInlineMethods().size());
            assertEquals(1, typeARefs.getContracts().size());
            ProofMetaPerTypeReferences typeMainRefs = ptRefs.get("Main");
            assertEquals(0, typeMainRefs.getAxioms().size());
            assertEquals(0, typeMainRefs.getInvariants().size());
            assertEquals(0, typeMainRefs.getAccesses().size());
            assertEquals(1, typeMainRefs.getInlineMethods().size());
            assertEquals(0, typeMainRefs.getContracts().size());
         }
         else {
            assertEquals(null, refs.getContract());
            assertEquals(0, refs.getPerTypeReferences().size());
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
