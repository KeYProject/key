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

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.testGeneration.EclipseTestGenerator;
import org.key_project.key4eclipse.resources.builder.TestSuiteGenerator;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.test.TestZ3;

public class BuilderTests extends AbstractResourceTest {
   
   //Disables the option "buildProofs". Expects no proofs to be build at all.
   @Test
   public void testBuildDisabled() throws CoreException, InterruptedException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testBuildDisabled", false, false, false, false, 1, false, false, false);
      testBuildDisabled(project);
      project.close(null);
   }
   
   
   //Runs a cleanBuild. Expects all proofs to be run again but doesn't deletes them initially.
   @Test
   public void testFullBuildSingleThreadCleanBuild() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadCleanBuild", true, false, false, false, 1, false, false, false);
      testCleanBuild(project);
      project.close(null);
   }
   @Test
   public void testFullBuildMultipleThreadsCleanBuild() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsCleanBuild", true, false, false, true, 2, false, false, false);
      testCleanBuild(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildSingleThreadCleanBuild() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadCleanBuild", true, false, true, false, 1, false, false, false);
      testCleanBuild(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsCleanBuild() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsCleanBuild", true, false, true, true, 2, false, false, false);
      testCleanBuild(project);
      project.close(null);
   }
   
   
   //Changes a single proof file. Expectations:
   //                                - Full Build: All proofs are done again
   //                                - Efficient Build: Just the proof associated with the changed proof file is done again
   @Test
   public void testFullBuildSingleThreadProofFileChanged() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadProofFileChanged", true, false, false, false, 1, false, false, false);
      testProofFileChanged(project);
      project.close(null);
   }
   @Test
   public void testFullBuildMultipleThreadsProofFileChanged() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsProofFileChanged", true, false, false, true, 2, false, false, false);
      testProofFileChanged(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildSingleThreadProofFileChanged() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadProofFileChanged", true, false, true, false, 1, false, false, false);
      testProofFileChanged(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsProofFileChanged() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsProofFileChanged", true, false, true, true, 2, false, false, false);
      testProofFileChanged(project);
      project.close(null);
   }
   
   
   //Deletes a proof file. Expectations are:
   //                         - Full Build: All proofs are done again
   //                         - Efficient Build: Just the proof associated with the deleted file is done again
   @Test
   public void testFullBuildSingleThreadProofFileDeleted() throws CoreException, InterruptedException {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadProofFileDeleted", true, false, false, false, 1, false, false, false);
      testFileDeleted(project, true);
      project.close(null);
   }
   @Test
   public void testFullBuildMultipleThreadsProofFileDeleted() throws CoreException, InterruptedException {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsProofFileDeleted", true, false, false, true, 2, false, false, false);
      testFileDeleted(project, true);
      project.close(null);
   }
   @Test
   public void testEfficientBuildSingleThreadProofFileDeleted() throws CoreException, InterruptedException {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadProofFileDeleted", true, false, true, false, 1, false, false, false);
      testFileDeleted(project, true);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsProofFileDeleted() throws CoreException, InterruptedException {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsProofFileDeleted", true, false, true, true, 2, false, false, false);
      testFileDeleted(project, true);
      project.close(null);
   }
   

   //Deletes a meta file. Expectations are:
   //                         - Full Build: All proofs are done again
   //                         - Efficient Build: Just the proof associated with the deleted file is done again
   @Test
   public void testFullBuildSingleThreadMetaFileDeleted() throws CoreException, InterruptedException {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadMetaFileDeleted", true, false, false, false, 1, false, false, false);
      testFileDeleted(project, false);
      project.close(null);
   }
   @Test
   public void testFullBuildMultipleThreadsMetaFileDeleted() throws CoreException, InterruptedException {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsMetaFileDeleted", true, false, false, true, 2, false, false, false);
      testFileDeleted(project, false);
      project.close(null);
   }
   @Test
   public void testEfficientBuildSingleThreadMetaFileDeleted() throws CoreException, InterruptedException {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadMetaFileDeleted", true, false, true, false, 1, false, false, false);
      testFileDeleted(project, false);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsMetaFileDeleted() throws CoreException, InterruptedException {
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsMetaFileDeleted", true, false, true, true, 2, false, false, false);
      testFileDeleted(project, false);
      project.close(null);
   }
   
      
   //Applies a trivial change to a java file. Expectations:
   //                                            - Full Build: Proof is done again
   //                                            - Efficient Build: Proof is not done again
   @Test
   public void testFullBuildSingleThreadChangeJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadChangeJavaFileTriveal", true, false, false, false, 1, false, false, false);
      testChangeJavaFileTriveal(project);
      project.close(null);
   }
   @Test
   public void testFullBuildMultipleThreadsChangeJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsChangeJavaFileTriveal", true, false, false, true, 2, false, false, false);
      testChangeJavaFileTriveal(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildSingleThreadChangeJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeJavaFileTriveal", true, false, true, false, 1, false, false, false);
      testChangeJavaFileTriveal(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeJavaFileTriveal", true, false, true, true, 2, false, false, false);
      testChangeJavaFileTriveal(project);
      project.close(null);
   }
   
   
   //Applies a trivial change to one of two java files. Expectations:
   //                                            - Full Build: All proof are done again
   //                                            - Efficient Build: No proof is done again
   @Test
   public void testFullBuildSingleThreadChangeSecondJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildSingleThreadChangeSecondJavaFileTriveal", true, false, false, false, 1, false, false, false);
      testChangeSecondJavaFileTrivial(project);
      project.close(null);
   }
   @Test
   public void testFullBuildMultipleThreadsChangeSecondJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testFullBuildMultipleThreadsChangeSecondJavaFileTriveal", true, false, false, true, 2, false, false, false);
      testChangeSecondJavaFileTrivial(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildSingleThreadChangeSecondJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeSecondJavaFileTriveal", true, false, true, false, 1, false, false, false);
      testChangeSecondJavaFileTrivial(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeSecondJavaFileTriveal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeSecondJavaFileTriveal", true, false, true, true, 2, false, false, false);
      testChangeSecondJavaFileTrivial(project);
      project.close(null);
   }
   
   
   //Adds a second method with a contract. 
   //Expectation: Just the new proof is done.
   @Test
   public void testEfficientBuildSingleThreadAddMethodWithContract() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadAddMethodWithContract", true, false, true, false, 1, false, false, false);
      testAddMethodWithContract(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsAddMethodWithContract() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsAddMethodWithContract", true, false, true, true, 2, false, false, false);
      testAddMethodWithContract(project);
      project.close(null);
   }
   
   
   //Adds a second file containing one method with a contract. 
   //Expectation: Just the new proof is done.
   @Test
   public void testEfficientBuildSingleThreadAddSecondJavaFileWithProof() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadAddSecondJavaFileWithProof", true, false, true, false, 1, false, false, false);
      testAddSecondJavaFileWithProof(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsAddSecondJavaFileWithProof() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsAddSecondJavaFileWithProof", true, false, true, true, 2, false, false, false);
      testAddSecondJavaFileWithProof(project);
      project.close(null);
   }
   
   
   //Adds another contract to a method.
   //Expectation: Just the new proof is done.
   @Test
   public void testEfficientBuildSingleThreadAddSecondContractToMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadAddSecondContractToMethod", true, false, true, false, 1, false, false, false);
      testAddSecondContractToMethod(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsAddSecondContractToMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsAddSecondContractToMethod", true, false, true, true, 2, false, false, false);
      testAddSecondContractToMethod(project);
      project.close(null);
   }
   

   //Changes one contract of a method.
   //Expectation: Just the changed proof is done.
   @Test
   public void testEfficientBuildSingleThreadChangeContractOfMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeContractOfMethod", true, false, true, false, 1, false, false, false);
      testChangeContractOfMethod(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeContractOfMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeContractOfMethod", true, false, true, true, 2, false, false, false);
      testChangeContractOfMethod(project);
      project.close(null);
   }
   
   
   
   
   //ProofReferencesTests
   
   
   //InlineMethod reference
   
   
   //Changes an in-lined method (the method itself).
   //Expectation: The proof of the method is done again
   @Test
   public void testEfficientBuildSingleThreadChangeInlinedMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeMethodOfProof", true, false, true, false, 1, false, false, false);
      testChangeInlinedMethod(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeInlinedMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeMethodOfProof", true, false, true, true, 2, false, false, false);
      testChangeInlinedMethod(project);
      project.close(null);
   }
   
   
   //CallMethod reference

   
   //Changes an called method.
   //Expectation: The proof of the method is done again
   @Test
   public void testEfficientBuildSingleThreadChangeCalledMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeCalledMethod", true, false, true, false, 1, false, false, false);
      testChangeCalledMethod(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeCalledMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeCalledMethod", true, false, true, true, 2, false, false, false);
      testChangeCalledMethod(project);
      project.close(null);
   }
   

   //Changes an called method in an other class.
   //Expectation: The proof of the method is done again
   @Test
   public void testEfficientBuildSingleThreadChangeCalledMethodInOtherClass() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeCalledMethodInOtherClass", true, false, true, false, 1, false, false, false);
      testChangeCalledMethodInOtherClass(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeCalledMethodInOtherClass() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeCalledMethodInOtherClass", true, false, true, true, 2, false, false, false);
      testChangeCalledMethodInOtherClass(project);
      project.close(null);
   }
   
   
   //Change called method's sub implementation
   //Expectation: The proof of the method is done again
   @Test
   public void testEfficientBuildSingleThreadChangeCalledMethodSubImplementation() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeCalledMethodSubImplementation", true, false, true, false, 1, false, false, false);
      testChangeCalledMethodSubImplementation(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeCalledMethodSubImplementation() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeCalledMethodSubImplementation", true, false, true, true, 2, false, false, false);
      testChangeCalledMethodSubImplementation(project);
      project.close(null);
   }
   
   
   //Add called method's sub implementation
   //Expectation: The proof of the method is done again
   @Test
   public void testEfficientBuildSingleThreadAddCalledMethodSubImplementation() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadAddCalledMethodSubImplementation", true, false, true, false, 1, false, false, false);
      testAddCalledMethodSubImplementation(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsAddCalledMethodSubImplementation() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsAddCalledMethodSubImplementation", true, false, true, true, 2, false, false, false);
      testAddCalledMethodSubImplementation(project);
      project.close(null);
   }
   
   
   //Removes called method's sub implementation
   //Expectation: The proof of the method is done again
   @Test
   public void testEfficientBuildSingleThreadRemoveCalledSubMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadRemoveCalledSubMethod", true, false, true, false, 1, false, false, false);
      testRemoveCalledMethodSubImplementation(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsRemoveCalledSubMethod() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsRemoveCalledSubMethod", true, false, true, true, 2, false, false, false);
      testRemoveCalledMethodSubImplementation(project);
      project.close(null);
   }
   
   
   //Removes called method's sub implementation class
   //Expectation: The proof of the method is done again
   @Test
   public void testEfficientBuildSingleThreadRemoveCalledMethodSubImplementationClass() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadRemoveCalledMethodSubImplementationClass", true, false, true, false, 1, false, false, false);
      testRemoveCalledMethodSubImplementationClass(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsRemoveCalledMethodSubImplementationClass() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsRemoveCalledMethodSubImplementationClass", true, false, true, true, 2, false, false, false);
      testRemoveCalledMethodSubImplementationClass(project);
      project.close(null);
   }
   
   
   //Access reference

   
   //Changes a used local field.
   //Expectation: The proof using the field is done again
   @Test
   public void testEfficientBuildSingleThreadChangeFieldLocal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeFieldLocal", true, false, true, false, 1, false, false, false);
      testChangeFieldLocal(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeFieldLocal() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeFieldLocal", true, false, true, true, 2, false, false, false);
      testChangeFieldLocal(project);
      project.close(null);
   }
   
   
   //Changes a used field in another class.
   //Expectation: The proof using the field is done again
   @Test
   public void testEfficientBuildSingleThreadChangeFieldInOtherClass() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeFieldInOtherClass", true, false, true, false, 1, false, false, false);
      testChangeFieldInOtherClass(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeFieldInOtherClass() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeFieldInOtherClass", true, false, true, true, 2, false, false, false);
      testChangeFieldInOtherClass(project);
      project.close(null);
   }
   
   
   //Contract reference
   
   
   //Changes a used contract
   //Expectation: The proof using the contract, and the proof associated with the used contract are done again
   @Test
   public void testEfficientBuildSingleThreadChangeUsedContract() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeUsedContract", true, false, true, false, 1, false, false, false);
      testChangeUsedContract(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeUsedContract() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeUsedContract", true, false, true, true, 2, false, false, false);
      testChangeUsedContract(project);
      project.close(null);
   }
   
   
   //Axiom reference
   
   
   //Changes an axiom
   //Expectation: All proofs using the axiom are done again
   @Test
   public void testEfficientBuildSingleThreadChangeAxiom() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeAxiom", true, false, true, false, 1, false, false, false);
      testChangeAxiom(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeAxiom() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeAxiom", true, false, true, true, 2, false, false, false);
      testChangeAxiom(project);
      project.close(null);
   }
   
   
   //Invariant reference
   //Expectation: All proofs using the invariant are done again
   @Test
   public void testEfficientBuildSingleThreadChangeInvariant() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadChangeInvariant", true, false, true, false, 1, false, false, false);
      testChangeInvariant(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsChangeInvariant() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsChangeInvariant", true, false, true, true, 2, false, false, false);
      testChangeInvariant(project);
      project.close(null);
   }
   
   //Overload
   //Expectation: Proofs using overloaded methods should be done again
   @Test
   public void testEfficientBuildSingleThreadAddOverload() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildSingleThreadAddOverload", true, false, true, false, 1, false, false, false);
      testAddOverload(project);
      project.close(null);
   }
   @Test
   public void testEfficientBuildMultipleThreadsAddOverload() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("BuilderTests_testEfficientBuildMultipleThreadsAddOverload", true, false, true, true, 2, false, false, false);
      testAddOverload(project);
      project.close(null);
   }
   
   
   //Test Case Generation Tests
   //The Z3 solver path ({@code z3SolverPath}) needs to be set
   //Just add the VM argument -Dz3SolverPath="PathToZ3Solver"
   
   @Test
   public void testFullBuildSingleThreadGenerateTestCases() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testFullBuildSingleThreadGenerateTestCases", true, false, false, false, 1, false, true, false);
      testTestCaseGeneration(project, false);
      project.close(null);
   }
//   @Test
//   public void testFullBuildMultipleThreadsGenerateTestCases() throws CoreException, InterruptedException, IOException{
//      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testFullBuildMultipleThreadsGenerateTestCases", true, false, false, true, 2, false, true, false);
//      testTestCaseGeneration(project, false);
//      project.close(null);
//   }
   @Test
   public void testEfficientBuildSingleThreadGenerateTestCases() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testEfficientBuildSingleThreadGenerateTestCases", true, false, true, false, 1, false, true, false);
      testTestCaseGeneration(project, false);
      project.close(null);
   }
//   @Test
//   public void testEfficientBuildMultipleThreadsGenerateTestCases() throws CoreException, InterruptedException, IOException{
//      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testEfficientBuildMultipleThreadsGenerateTestCases", true, false, true, true, 2, false, true, false);
//      testTestCaseGeneration(project, false);
//      project.close(null);
//   }
   
   @Test
   public void testFullBuildSingleThreadGenerateTestCasesAutoDelete() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testFullBuildSingleThreadGenerateTestCasesAutoDelete", true, false, false, false, 1, false, true, true);
      testTestCaseGeneration(project, true);
      project.close(null);
   }
//   @Test
//   public void testFullBuildMultipleThreadsGenerateTestCasesAutoDelete() throws CoreException, InterruptedException, IOException{
//      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testFullBuildMultipleThreadsGenerateTestCasesAutoDelete", true, false, false, true, 2, false, true, true);
//      testTestCaseGeneration(project, true);
//      project.close(null);
//   }
   @Test
   public void testEfficientBuildSingleThreadGenerateTestCasesAutoDelete() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testEfficientBuildSingleThreadGenerateTestCasesAutoDelete", true, false, true, false, 1, false, true, true);
      testTestCaseGeneration(project, true);
      project.close(null);
   }
//   @Test
//   public void testEfficientBuildMultipleThreadsGenerateTestCasesAutoDelete() throws CoreException, InterruptedException, IOException{
//      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testEfficientBuildMultipleThreadsGenerateTestCasesAutoDelete", true, false, true, true, 2, false, true, true);
//      testTestCaseGeneration(project, true);
//      project.close(null);
//   }
   
   //Test Suite Generation Tests
   //The Z3 solver path ({@code z3SolverPath}) needs to be set
   //Just add the VM argument -Dz3SolverPath="PathToZ3Solver"
   @Test
   public void testFullBuildSingleThreadGenerateTestSuite() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testFullBuildSingleThreadGenerateTestSuite", true, false, false, false, 1, false, true, false);
      testTestSuiteGeneration(project, false);
      project.close(null);
   }
//   @Test
//   public void testFullBuildMultipleThreadsGenerateTestSuite() throws CoreException, InterruptedException, IOException{
//      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testFullBuildMultipleThreadsGenerateTestSuite", true, false, false, true, 2, false, true, false);
//      testTestSuiteGeneration(project, false);
//      project.close(null);
//   }
   @Test
   public void testEfficientBuildSingleThreadGenerateTestSuite() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testEfficientBuildSingleThreadGenerateTestSuite", true, false, true, false, 1, false, true, false);
      testTestSuiteGeneration(project, false);
      project.close(null);
   }
//   @Test
//   public void testEfficientBuildMultipleThreadsGenerateTestSuite() throws CoreException, InterruptedException, IOException{
//      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testEfficientBuildMultipleThreadsGenerateTestSuite", true, false, true, true, 2, false, true, false);
//      testTestSuiteGeneration(project, false);
//      project.close(null);
//   }

   @Test
   public void testFullBuildSingleThreadGenerateTestSuiteAutoDelete() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testFullBuildSingleThreadGenerateTestSuiteAutoDelete", true, false, false, false, 1, false, true, true);
      testTestSuiteGeneration(project, true);
      project.close(null);
   }
//   @Test
//   public void testFullBuildMultipleThreadsGenerateTestSuiteAutoDelete() throws CoreException, InterruptedException, IOException{
//      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testFullBuildMultipleThreadsGenerateTestSuiteAutoDelete", true, false, false, true, 2, false, true, true);
//      testTestSuiteGeneration(project, true);
//      project.close(null);
//   }
   @Test
   public void testEfficientBuildSingleThreadGenerateTestSuiteAutoDelete() throws CoreException, InterruptedException, IOException{
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testEfficientBuildSingleThreadGenerateTestSuiteAutoDelete", true, false, true, false, 1, false, true, true);
      testTestSuiteGeneration(project, true);
      project.close(null);
   }
//   @Test
//   public void testEfficientBuildMultipleThreadsGenerateTestSuiteAutoDelete() throws CoreException, InterruptedException, IOException{
//      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("testEfficientBuildMultipleThreadsGenerateTestSuiteAutoDelete", true, false, true, true, 2, false, true, true);
//      testTestSuiteGeneration(project, true);
//      project.close(null);
//   }


   private void testBuildDisabled(IProject project) throws CoreException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("buildDisabled").append("File.java"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testBuildDisabled", project.getFolder("src"));

      assertTrue(javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
   }
   
   
   private void testCleanBuild(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("cleanBuild").append("File.java"));
      final IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("cleanBuild").append("File.java").append("cleanBuild_File[cleanBuild_File__add(int,int)]_JML_operation_contract_0.proof"));
      final IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testCleanBuild/src", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testCleanBuild/customProof.proof");
      proofFile.setContents(is, IResource.FORCE, null);
      is.close();
      KeY4EclipseResourcesTestUtil.build(project);
      
      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      KeY4EclipseResourcesTestUtil.cleanBuildResourceChangeListener listener = new KeY4EclipseResourcesTestUtil.cleanBuildResourceChangeListener(proofFile, metaFile);
      ResourcesPlugin.getWorkspace().addResourceChangeListener(listener);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      KeY4EclipseResourcesTestUtil.cleanBuild(project);
      
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFile.getLocalTimeStamp() != proofFileModStamp);
      assertTrue(metaFile.getLocalTimeStamp() != metaFileModStamp);
      assertFalse(listener.getDeleted());
      ResourcesPlugin.getWorkspace().removeResourceChangeListener(listener);
   }
   

   private void testAddMethodWithContract(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddMethodWithContract/File.java", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      long proofFile0modStamp = proofFile0.getLocalTimeStamp();
      long metaFile0modStamp = metaFile0.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testAddMethodWithContract/ChangedFile.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      assertTrue(proofFile0modStamp == proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0modStamp == metaFile0.getLocalTimeStamp());
      
   }

   
   private void testAddSecondContractToMethod(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_normal_behavior_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_normal_behavior_operation_contract_1.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddSecondContractToMethod/File.java", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      long proofFile0modStamp = proofFile0.getLocalTimeStamp();
      long metaFile0modStamp = metaFile0.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testAddSecondContractToMethod/ChangedFile.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      assertTrue(proofFile0modStamp == proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0modStamp == metaFile0.getLocalTimeStamp());
      
   }
   
   private void testChangeContractOfMethod(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_normal_behavior_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_normal_behavior_operation_contract_1.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeContractOfMethod/File.java", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      long proofFile0modStamp = proofFile0.getLocalTimeStamp();
      long metaFile0modStamp = metaFile0.getLocalTimeStamp();
      long proofFile1modStamp = proofFile1.getLocalTimeStamp();
      long metaFile1modStamp = metaFile1.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeContractOfMethod/ChangedFile.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      assertTrue(proofFile0modStamp == proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0modStamp == metaFile0.getLocalTimeStamp());
      assertTrue(proofFile1modStamp != proofFile1.getLocalTimeStamp());
      assertTrue(metaFile1modStamp != metaFile1.getLocalTimeStamp());
      
   }
   
   private void testAddSecondJavaFileWithProof(IProject project) throws CoreException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File0.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File1.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File0.java").append("File0[File0__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File1.java").append("File1[File1__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddSecondJavaFileWithProof/File0.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && !javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && !javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());

      long proofFile0modStamp = proofFile0.getLocalTimeStamp();
      long metaFile0modStamp = metaFile0.getLocalTimeStamp();
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddSecondJavaFileWithProof/File1.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      assertTrue(proofFile0modStamp == proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0modStamp == metaFile0.getLocalTimeStamp());
   }

   private void testChangeJavaFileTriveal(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("file").append("to").append("change").append("File.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("file").append("to").append("change").append("File.java").append("file_to_change_File[file_to_change_File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeJavaFileTriveal", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());
      
      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeJavaFileTriveal/file/to/change/File.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      if(KeYProjectProperties.isEnableBuildRequiredProofsOnly(project)){
         assertTrue(proofFileModStamp == proofFile.getLocalTimeStamp());
         assertTrue(metaFileModStamp == metaFile.getLocalTimeStamp());
      }
      else{
         assertTrue(proofFileModStamp != proofFile.getLocalTimeStamp());
         assertTrue(metaFileModStamp != metaFile.getLocalTimeStamp());
      }
   }
   
   private void testChangeSecondJavaFileTrivial(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("file").append("to").append("change").append("File0.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("file").append("to").append("change").append("File1.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("file").append("to").append("change").append("File0.java").append("file_to_change_File0[file_to_change_File0__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("file").append("to").append("change").append("File1.java").append("file_to_change_File1[file_to_change_File1__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeSecondJavaFileTrivial/", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      
      long proofFile0modStamp = proofFile0.getLocalTimeStamp();
      long metaFile0modStamp = metaFile0.getLocalTimeStamp();
      long proofFile1modStamp = proofFile1.getLocalTimeStamp();
      long metaFile1modStamp = metaFile1.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeSecondJavaFileTrivial/file/to/change/File0.java");
      javaFile0.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      if(KeYProjectProperties.isEnableBuildRequiredProofsOnly(project)){
         assertTrue(proofFile0modStamp == proofFile0.getLocalTimeStamp());
         assertTrue(metaFile0modStamp == metaFile0.getLocalTimeStamp());
         
         assertTrue(proofFile1modStamp == proofFile1.getLocalTimeStamp());
         assertTrue(metaFile1modStamp == metaFile1.getLocalTimeStamp());
      }
      else{
         assertTrue(proofFile0modStamp != proofFile0.getLocalTimeStamp());
         assertTrue(metaFile0modStamp != metaFile0.getLocalTimeStamp());
         
         assertTrue(proofFile1modStamp != proofFile1.getLocalTimeStamp());
         assertTrue(metaFile1modStamp != metaFile1.getLocalTimeStamp());  
      }
   }
   
   
   private void testFileDeleted(IProject project, boolean deleteProof) throws CoreException{
//      ResourcesPlugin.getWorkspace().addResourceChangeListener(listener, IProject.b)
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists());
      assertTrue(!proofFile1.exists());
      assertTrue(!metaFile0.exists());
      assertTrue(!metaFile1.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testFileDeleted/", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists());
      assertTrue(proofFile1.exists());
      assertTrue(metaFile0.exists());
      assertTrue(metaFile1.exists());

      long proofFile0TimeStamp = proofFile0.getLocalTimeStamp();
      long proofFile1TimeStamp = proofFile1.getLocalTimeStamp();
      long metaFile0TimeStamp = metaFile0.getLocalTimeStamp();
      long metaFile1TimeStamp = metaFile1.getLocalTimeStamp();

      if(deleteProof){
         proofFile0.delete(IResource.FORCE, null);
         assertTrue(!proofFile0.exists());
      }
      else{
         metaFile0.delete(IResource.FORCE, null);
         assertTrue(!metaFile0.exists());
      }
      
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists());
      assertTrue(proofFile1.exists());
      assertTrue(metaFile0.exists());
      assertTrue(metaFile1.exists());
      
      if (KeYProjectProperties.isEnableBuildRequiredProofsOnly(project)) {
         assertTrue(proofFile0TimeStamp != proofFile0.getLocalTimeStamp());
         assertTrue(proofFile1TimeStamp == proofFile1.getLocalTimeStamp());
         assertTrue(metaFile0TimeStamp != metaFile0.getLocalTimeStamp());
         assertTrue(metaFile1TimeStamp == metaFile1.getLocalTimeStamp());
      }
      else {
         assertTrue(proofFile0TimeStamp != proofFile0.getLocalTimeStamp());
         assertTrue(proofFile1TimeStamp != proofFile1.getLocalTimeStamp());
         assertTrue(metaFile0TimeStamp != metaFile0.getLocalTimeStamp());
         assertTrue(metaFile1TimeStamp != metaFile1.getLocalTimeStamp());
      }
   }
   
   
   private void testProofFileChanged(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testProofFileChanged/File.java", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      
      long proofFile0modStamp = proofFile0.getLocalTimeStamp();
      long metaFile0modStamp = metaFile0.getLocalTimeStamp();
      long proofFile1modStamp = proofFile1.getLocalTimeStamp();
      long metaFile1modStamp = metaFile1.getLocalTimeStamp();
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testProofFileChanged/proofFile0.proof");
      proofFile0.setContents(is, IResource.FORCE, null);
      is.close();

      assertTrue(proofFile0modStamp != proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0modStamp == metaFile0.getLocalTimeStamp());
      assertTrue(proofFile1modStamp == proofFile1.getLocalTimeStamp());
      assertTrue(metaFile1modStamp == metaFile1.getLocalTimeStamp());
      
      proofFile0modStamp = proofFile0.getLocalTimeStamp();
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      if (KeYProjectProperties.isEnableBuildRequiredProofsOnly(project)) {
         assertTrue(proofFile0modStamp != proofFile0.getLocalTimeStamp());
         assertTrue(metaFile0modStamp != metaFile0.getLocalTimeStamp());
         assertTrue(proofFile1modStamp == proofFile1.getLocalTimeStamp());
         assertTrue(metaFile1modStamp == metaFile1.getLocalTimeStamp());
      }
      else {
         assertTrue(proofFile0modStamp != proofFile0.getLocalTimeStamp());
         assertTrue(metaFile0modStamp != metaFile0.getLocalTimeStamp());
         assertTrue(proofFile1modStamp != proofFile1.getLocalTimeStamp());
         assertTrue(metaFile1modStamp != metaFile1.getLocalTimeStamp());
      }
   }
   
   
   private void testChangeInlinedMethod(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeInLinedMethod/File.java", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      long proofFile0ModStamp = proofFile0.getLocalTimeStamp();
      long metaFile0ModStamp = metaFile0.getLocalTimeStamp();
      long proofFile1ModStamp = proofFile1.getLocalTimeStamp();
      long metaFile1ModStamp = metaFile1.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeInLinedMethod/ChangedFile.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      assertTrue(proofFile0ModStamp != proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0ModStamp != metaFile0.getLocalTimeStamp());
      assertTrue(proofFile1ModStamp == proofFile1.getLocalTimeStamp());
      assertTrue(metaFile1ModStamp == metaFile1.getLocalTimeStamp());
   }
   
   
   private void testChangeCalledMethod(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeCalledMethod/File.java", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeCalledMethod/ChangedFile.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFileModStamp != proofFile.getLocalTimeStamp());
      assertTrue(metaFileModStamp != metaFile.getLocalTimeStamp());
   }
   
   
   private void testChangeCalledMethodInOtherClass(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File0.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File1.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File0.java").append("File0[File0__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeCalledMethodInOtherClass/File0.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeCalledMethodInOtherClass/File1.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeCalledMethodInOtherClass/ChangedFile1.java");
      javaFile1.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFileModStamp != proofFile.getLocalTimeStamp());
      assertTrue(metaFileModStamp != metaFile.getLocalTimeStamp());
   }
   
   
   private void testChangeCalledMethodSubImplementation(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File0.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File1.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File2.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File0.java").append("File0[File0__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists() && !javaFile2.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeCalledMethodSubImplementation/File0.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeCalledMethodSubImplementation/File1.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeCalledMethodSubImplementation/File2.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeCalledMethodSubImplementation/ChangedFile2.java");
      javaFile2.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFileModStamp != proofFile.getLocalTimeStamp());
      assertTrue(metaFileModStamp != metaFile.getLocalTimeStamp());
   }
   
   
   private void testAddCalledMethodSubImplementation(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File0.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File1.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File2.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File0.java").append("File0[File0__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists() && !javaFile2.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddCalledMethodSubImplementation/File0.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddCalledMethodSubImplementation/File1.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddCalledMethodSubImplementation/File2.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testAddCalledMethodSubImplementation/ChangedFile2.java");
      javaFile2.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFileModStamp != proofFile.getLocalTimeStamp());
      assertTrue(metaFileModStamp != metaFile.getLocalTimeStamp());
   }
   
   
   private void testRemoveCalledMethodSubImplementation(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File0.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File1.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File2.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File0.java").append("File0[File0__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists() && !javaFile2.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testRemoveCalledMethodSubImplementation/File0.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testRemoveCalledMethodSubImplementation/File1.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testRemoveCalledMethodSubImplementation/File2.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testRemoveCalledMethodSubImplementation/ChangedFile2.java");
      javaFile2.setContents(is, IResource.FORCE, null);
      is.close();
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFileModStamp != proofFile.getLocalTimeStamp());
      assertTrue(metaFileModStamp != metaFile.getLocalTimeStamp());
   }
   
   
   private void testRemoveCalledMethodSubImplementationClass(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File0.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File1.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File2.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File0.java").append("File0[File0__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists() && !javaFile2.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testRemoveCalledMethodSubImplementationClass/File0.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testRemoveCalledMethodSubImplementationClass/File1.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testRemoveCalledMethodSubImplementationClass/File2.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      javaFile2.delete(true, null);
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists() && !javaFile2.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFileModStamp != proofFile.getLocalTimeStamp());
      assertTrue(metaFileModStamp != metaFile.getLocalTimeStamp());
   }
   
   
   private void testChangeFieldLocal(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeFieldLocal/File.java", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeFieldLocal/ChangedFile.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFileModStamp == proofFile.getLocalTimeStamp());
      assertTrue(metaFileModStamp == metaFile.getLocalTimeStamp());
   }
   
   
   private void testChangeFieldInOtherClass(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File0.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File1.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File0.java").append("File0[File0__add(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeFieldInOtherClass/File0.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeFieldInOtherClass/File1.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeFieldInOtherClass/ChangedFile1.java");
      javaFile1.setContents(is, IResource.FORCE, null);
      is.close();
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFileModStamp == proofFile.getLocalTimeStamp());
      assertTrue(metaFileModStamp == metaFile.getLocalTimeStamp());
   }
   
   
   private void testChangeUsedContract(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File.java").append("File[File__identity(int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile2 = KeY4EclipseResourcesTestUtil.getFile(proofFile2.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      assertTrue(!proofFile2.exists() && !metaFile2.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeUsedContract/File.java", project.getFolder("src"));
      
      assertTrue(javaFile.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      assertTrue(proofFile2.exists() && metaFile2.exists());

      long proofFile0ModStamp = proofFile0.getLocalTimeStamp();
      long metaFile0ModStamp = metaFile0.getLocalTimeStamp();
      long proofFile1ModStamp = proofFile1.getLocalTimeStamp();
      long metaFile1ModStamp = metaFile1.getLocalTimeStamp();
      long proofFile2ModStamp = proofFile2.getLocalTimeStamp();
      long metaFile2ModStamp = metaFile2.getLocalTimeStamp();
      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeUsedContract/ChangedFile.java");
      javaFile.setContents(is, IResource.FORCE, null);
      is.close();
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      assertTrue(proofFile2.exists() && metaFile2.exists());

      assertTrue(proofFile0ModStamp != proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0ModStamp != metaFile0.getLocalTimeStamp());
      assertTrue(proofFile1ModStamp == proofFile1.getLocalTimeStamp());
      assertTrue(metaFile1ModStamp == metaFile1.getLocalTimeStamp());
      assertTrue(proofFile2ModStamp != proofFile2.getLocalTimeStamp());
      assertTrue(metaFile2ModStamp != metaFile2.getLocalTimeStamp());
   }
   

   private void testChangeAxiom(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File0.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("File1.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File0.java").append("File0[File0__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File0.java").append("File0[File0__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File1.java").append("File1[File1__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile3 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("File1.java").append("File1[File1__sub(int,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile2 = KeY4EclipseResourcesTestUtil.getFile(proofFile2.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile3 = KeY4EclipseResourcesTestUtil.getFile(proofFile3.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      assertTrue(!proofFile2.exists() && !metaFile2.exists());
      assertTrue(!proofFile3.exists() && !metaFile3.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeAxiom/File0.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeAxiom/File1.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      assertTrue(proofFile2.exists() && metaFile2.exists());
      assertTrue(proofFile3.exists() && metaFile3.exists());

      long proofFile0ModStamp = proofFile0.getLocalTimeStamp();
      long metaFile0ModStamp = metaFile0.getLocalTimeStamp();
      long proofFile1ModStamp = proofFile1.getLocalTimeStamp();
      long metaFile1ModStamp = metaFile1.getLocalTimeStamp();
      long proofFile2ModStamp = proofFile2.getLocalTimeStamp();
      long metaFile2ModStamp = metaFile2.getLocalTimeStamp();
      long proofFile3ModStamp = proofFile3.getLocalTimeStamp();
      long metaFile3ModStamp = metaFile3.getLocalTimeStamp();

      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeAxiom/ChangedFile.java");
      javaFile0.setContents(is, IResource.FORCE, null);
      is.close();
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      assertTrue(proofFile2.exists() && metaFile2.exists());
      assertTrue(proofFile3.exists() && metaFile3.exists());

      assertTrue(proofFile0ModStamp != proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0ModStamp != metaFile0.getLocalTimeStamp());
      assertTrue(proofFile1ModStamp != proofFile1.getLocalTimeStamp());
      assertTrue(metaFile1ModStamp != metaFile1.getLocalTimeStamp());
      assertTrue(proofFile2ModStamp == proofFile2.getLocalTimeStamp());
      assertTrue(metaFile2ModStamp == metaFile2.getLocalTimeStamp());
      assertTrue(proofFile3ModStamp == proofFile3.getLocalTimeStamp());
      assertTrue(metaFile3ModStamp == metaFile3.getLocalTimeStamp());
   }
   

   private void testChangeInvariant(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("Child.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("InvariantInOperationContract.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("Child.java").append("Child[Child__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("InvariantInOperationContract.java").append("InvariantInOperationContract[InvariantInOperationContract__add(int,int)]_JML_operation_contract_0.proof"));
      IFile proofFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("InvariantInOperationContract.java").append("InvariantInOperationContract[InvariantInOperationContract__main(Child,int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile2 = KeY4EclipseResourcesTestUtil.getFile(proofFile2.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      assertTrue(!proofFile2.exists() && !metaFile2.exists());
      
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeInvariant/Child.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testChangeInvariant/InvariantInOperationContract.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      assertTrue(proofFile2.exists() && metaFile2.exists());

      long proofFile0ModStamp = proofFile0.getLocalTimeStamp();
      long metaFile0ModStamp = metaFile0.getLocalTimeStamp();
      long proofFile1ModStamp = proofFile1.getLocalTimeStamp();
      long metaFile1ModStamp = metaFile1.getLocalTimeStamp();
      long proofFile2ModStamp = proofFile2.getLocalTimeStamp();
      long metaFile2ModStamp = metaFile2.getLocalTimeStamp();

      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testChangeInvariant/ChangedChild.java");
      javaFile0.setContents(is, IResource.FORCE, null);
      is.close();
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      assertTrue(proofFile2.exists() && metaFile2.exists());

      assertTrue(proofFile0ModStamp != proofFile0.getLocalTimeStamp());
      assertTrue(metaFile0ModStamp != metaFile0.getLocalTimeStamp());
      assertTrue(proofFile1ModStamp == proofFile1.getLocalTimeStamp());
      assertTrue(metaFile1ModStamp == metaFile1.getLocalTimeStamp());
      assertTrue(proofFile2ModStamp != proofFile2.getLocalTimeStamp());
      assertTrue(metaFile2ModStamp != metaFile2.getLocalTimeStamp());
   }
   
   
   private void testAddOverload(IProject project) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("Main.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("A.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("B.java"));
      IFile proofFile = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("Main.java").append("Main[Main__main(B)]_JML_normal_behavior_operation_contract_0.proof"));
      IFile metaFile = KeY4EclipseResourcesTestUtil.getFile(proofFile.getFullPath().removeFileExtension().addFileExtension("proofmeta"));

      assertTrue(!javaFile0.exists() && !javaFile1.exists() && !javaFile2.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile.exists() && !metaFile.exists());
      

      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddOverload/Main.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddOverload/A.java", project.getFolder("src"));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testAddOverload/B.java", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      long proofFileModStamp = proofFile.getLocalTimeStamp();
      long metaFileModStamp = metaFile.getLocalTimeStamp();

      
      InputStream is = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testAddOverload/ChangedMain.java");
      javaFile0.setContents(is, IResource.FORCE, null);
      is.close();
      
      //build
      KeY4EclipseResourcesTestUtil.build(project);

      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile.exists() && metaFile.exists());

      assertTrue(proofFileModStamp != proofFile.getLocalTimeStamp());
      assertTrue(metaFileModStamp != metaFile.getLocalTimeStamp());
   }

   private void testTestCaseGeneration(IProject project, boolean autoDelete) throws CoreException, IOException{
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("A.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("testpackage").append("B.java"));
      IFile javaFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("testpackage").append("sub").append("sub").append("C.java"));
      IFile javaFile3 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("testpackage").append("sub").append("sub").append("D.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("A.java").append("A[A__id(int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("testpackage").append("B.java").append("testpackage_B[testpackage_B__id(int)]_JML_operation_contract_0.proof"));
      IFile proofFile2 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("testpackage").append("sub").append("sub").append("C.java").append("testpackage_sub_sub_C[testpackage_sub_sub_C__id(int)]_JML_operation_contract_0.proof"));
      IFile proofFile3 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("testpackage").append("sub").append("sub").append("D.java").append("testpackage_sub_sub_D[testpackage_sub_sub_D__id(int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile2 = KeY4EclipseResourcesTestUtil.getFile(proofFile2.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile3 = KeY4EclipseResourcesTestUtil.getFile(proofFile3.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      SolverType type = SolverType.Z3_CE_SOLVER;
      String solverPathProperty = System.getProperty(TestZ3.SYSTEM_PROPERTY_SOLVER_PATH);
      if (!StringUtil.isTrimmedEmpty(solverPathProperty)) {
         type.setSolverCommand(solverPathProperty);
      }
      assertTrue(SolverType.Z3_CE_SOLVER.isInstalled(true));

      assertTrue(!javaFile0.exists() && !javaFile1.exists() && !javaFile2.exists() && !javaFile3.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      assertTrue(!proofFile2.exists() && !metaFile2.exists());
      assertTrue(!proofFile3.exists() && !metaFile3.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testTestCaseGeneration/", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists() && javaFile3.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists() && javaFile3.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());
      assertTrue(proofFile2.exists() && metaFile2.exists());
      assertTrue(proofFile3.exists() && metaFile3.exists());
      
      IProject testProject = ResourcesPlugin.getWorkspace().getRoot().getProject(project.getName() + EclipseTestGenerator.TEST_PROJECT_SUFFIX);
      assertTrue(testProject.exists());
      assertTrue(testProject.isOpen());

      IJavaProject javaSourceProject = JavaCore.create(project);
      
      // Test library folder
      IFolder libFolder = testProject.getFolder(EclipseTestGenerator.LIB_FOLDER_NAME);
      assertTrue(libFolder.exists());
      IFile readmeFile = libFolder.getFile(EclipseTestGenerator.LIB_FOLDER_README_NAME);
      assertTrue(readmeFile.exists());
      assertEquals(IOUtil.readFrom(EclipseTestGenerator.createLibFolderReadmeContent()), ResourceUtil.readFrom(readmeFile));

      // Test log folder
      IFolder logFolder = testProject.getFolder(EclipseTestGenerator.LOG_FOLDER_NAME);
      assertTrue(logFolder.exists());
      IFile logFile0 = logFolder.getFile(JDTUtil.ensureValidJavaTypeName("A_A__id_int___JML_operation_contract_0", javaSourceProject) + EclipseTestGenerator.LOG_FILE_EXTENSION_WITH_DOT);
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(logFile0)));
      IFile logFile1 = logFolder.getFile(JDTUtil.ensureValidJavaTypeName("testpackage_B_testpackage_B__id_int___JML_operation_contract_0", javaSourceProject) + EclipseTestGenerator.LOG_FILE_EXTENSION_WITH_DOT);
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(logFile1)));
      IFile logFile2 = logFolder.getFile(JDTUtil.ensureValidJavaTypeName("testpackage_sub_sub_C_testpackage_sub_sub_C__id_int___JML_operation_contract_0", javaSourceProject) + EclipseTestGenerator.LOG_FILE_EXTENSION_WITH_DOT);
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(logFile2)));
      IFile logFile3 = logFolder.getFile(JDTUtil.ensureValidJavaTypeName("testpackage_sub_sub_D_testpackage_sub_sub_D__id_int___JML_operation_contract_0", javaSourceProject) + EclipseTestGenerator.LOG_FILE_EXTENSION_WITH_DOT);
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(logFile3)));

      // Test src folder
      IFolder srcFolder = testProject.getFolder(JDTUtil.getSourceFolderName());
      IFolder testPackageFolder = srcFolder.getFolder("testpackage");
      IFolder testPackageSubFolder = testPackageFolder.getFolder("sub");
      IFolder testPackageSubSubFolder = testPackageSubFolder.getFolder("sub");
      IFile testFile0 = srcFolder.getFile("A_A__id_int___JML_operation_contract_0.java");
      IFile testFile1 = testPackageFolder.getFile("testpackage_B_testpackage_B__id_int___JML_operation_contract_0.java");
      IFile testFile2 = testPackageSubSubFolder.getFile("testpackage_sub_sub_C_testpackage_sub_sub_C__id_int___JML_operation_contract_0.java");
      IFile testFile3 = testPackageSubSubFolder.getFile("testpackage_sub_sub_D_testpackage_sub_sub_D__id_int___JML_operation_contract_0.java");

      assertTrue(srcFolder.exists());
      assertTrue(testPackageFolder.exists());
      assertTrue(testPackageSubFolder.exists());
      assertTrue(testPackageSubSubFolder.exists());
      
      assertTrue(testFile0.exists() && testFile1.exists() && testFile2.exists() && testFile3.exists());

      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile0)));
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile1)));
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile2)));
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile3)));
      
      javaFile3.delete(true, null);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && javaFile2.exists() && !javaFile3.exists());
      
      assertTrue(srcFolder.exists());
      assertTrue(testPackageFolder.exists());
      assertTrue(testPackageSubFolder.exists());
      assertTrue(testPackageSubSubFolder.exists());
      assertTrue(testFile0.exists() && testFile1.exists() && testFile2.exists());
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile0)));
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile1)));
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile2)));
      
      if(autoDelete) {
         assertTrue(!testFile3.exists());
      }
      else {
         assertTrue(testFile3.exists());
         assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile3)));
      }
      
      javaFile2.delete(true, null);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists() && !javaFile2.exists() && !javaFile3.exists());
      
      assertTrue(srcFolder.exists());
      assertTrue(testPackageFolder.exists());
      assertTrue(testFile0.exists() && testFile1.exists());
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile0)));
      assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile1)));
      
      if(autoDelete) {
         assertTrue(!testPackageSubFolder.exists());
         assertTrue(!testPackageSubSubFolder.exists());
         assertTrue(!testFile2.exists() && !testFile3.exists());
      }
      else {
         assertTrue(testPackageSubFolder.exists());
         assertTrue(testPackageSubSubFolder.exists());
         assertTrue(testFile2.exists() && testFile3.exists());
         assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile0)));
         assertFalse(StringUtil.isTrimmedEmpty(ResourceUtil.readFrom(testFile1)));
      }
   }

   
   private void testTestSuiteGeneration(IProject project, boolean autoDelete) throws CoreException, IOException {
      IFolder proofFolder = KeY4EclipseResourcesTestUtil.getProofFolder(project);
      IFile javaFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("A.java"));
      IFile javaFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("src").append("testpackage").append("B.java"));
      IFile proofFile0 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("A.java").append("A[A__id(int)]_JML_operation_contract_0.proof"));
      IFile proofFile1 = KeY4EclipseResourcesTestUtil.getFile(
            project.getFullPath().append("proofs").append("testpackage").append("B.java").append("testpackage_B[testpackage_B__id(int)]_JML_operation_contract_0.proof"));
      IFile metaFile0 = KeY4EclipseResourcesTestUtil.getFile(proofFile0.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      IFile metaFile1 = KeY4EclipseResourcesTestUtil.getFile(proofFile1.getFullPath().removeFileExtension().addFileExtension("proofmeta"));
      
      SolverType type = SolverType.Z3_CE_SOLVER;
      String solverPathProperty = System.getProperty(TestZ3.SYSTEM_PROPERTY_SOLVER_PATH);
      if (!StringUtil.isTrimmedEmpty(solverPathProperty)) {
         type.setSolverCommand(solverPathProperty);
      }
      assertTrue(SolverType.Z3_CE_SOLVER.isInstalled(true));

      assertTrue(!javaFile0.exists() && !javaFile1.exists());
      KeY4EclipseResourcesTestUtil.assertCleanProofFolder(proofFolder);
      assertTrue(!proofFile0.exists() && !metaFile0.exists());
      assertTrue(!proofFile1.exists() && !metaFile1.exists());
      
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/BuilderTests/testTestSuiteGeneration/src/", project.getFolder("src"));
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      assertTrue(javaFile0.exists() && javaFile1.exists());
      assertTrue(proofFolder.exists());
      assertTrue(proofFile0.exists() && metaFile0.exists());
      assertTrue(proofFile1.exists() && metaFile1.exists());

      //Get Test Project
      IProject testProject = ResourcesPlugin.getWorkspace().getRoot().getProject(project.getName() + EclipseTestGenerator.TEST_PROJECT_SUFFIX);
      assertTrue(testProject.exists());
      assertTrue(testProject.isOpen());

      IFolder srcFolder = testProject.getFolder(JDTUtil.getSourceFolderName());
      IFile testSuite = srcFolder.getFile(TestSuiteGenerator.TESTSUITE_TYPENAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);
      
      assertTrue(srcFolder.exists());
      assertTrue(testSuite.exists());
      
      //Compare test suite
      InputStream in = BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/BuilderTests/testTestSuiteGeneration/Suite0");
      String expected = IOUtil.readFrom(in);
      String actual = ResourceUtil.readFrom(testSuite);
      TestUtilsUtil.assertEqualsIgnoreWhitespace(expected, actual);

      javaFile1.delete(true, null);
      
      KeY4EclipseResourcesTestUtil.build(project);
      
      //Compare test suite
      String compareFile = null;
      if(autoDelete) {
         compareFile = "data/BuilderTests/testTestSuiteGeneration/suite1";
      }
      else {
         compareFile = "data/BuilderTests/testTestSuiteGeneration/suite0";
      }
      in = BundleUtil.openInputStream(Activator.PLUGIN_ID, compareFile);
      expected = IOUtil.readFrom(in);
      actual = ResourceUtil.readFrom(testSuite);
      TestUtilsUtil.assertEqualsIgnoreWhitespace(expected, actual);
   }
}