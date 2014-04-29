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

package org.key_project.sed.ui.visualization.test.testcase;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.transaction.RecordingCommand;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.emf.transaction.util.TransactionUtil;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.ui.visualization.execution_tree.editor.ExecutionTreeDiagramEditor;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.test.util.TestVisualizationUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link ExecutionTreeUtil}
 * @author Martin Hentschel
 */
public class ExecutionTreeUtilTest extends AbstractSetupTestCase {
   /**
    * Tests {@link ExecutionTreeUtil#getAllDebugTargets(org.eclipse.graphiti.dt.IDiagramTypeProvider)}
    */
   @Test
   public void testGetAllDebugTargets() throws CoreException, IOException {
      // Test null
      ISEDDebugTarget[] targets = ExecutionTreeUtil.getAllDebugTargets(null);
      assertDebugTargets(targets);
      // Test diagram type provider without diagram
      final IDiagramTypeProvider typeProvider = GraphitiUi.getExtensionManager().createDiagramTypeProvider(ExecutionTreeDiagramTypeProvider.PROVIDER_ID);
      targets = ExecutionTreeUtil.getAllDebugTargets(typeProvider);
      assertDebugTargets(targets);
      // Test diagram type provider with diagram but without linked targets
      IProject project = TestUtilsUtil.createProject("ExecutionTreeUtilTest_testGetAllDebugTargets");
      IFile diagramFile = project.getFile("Diagram" + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT);
      IFile modelFile = project.getFile("Diagram" + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT);
      final Diagram diagram = TestVisualizationUtil.createEmptyExecutionTreeDiagram(diagramFile, modelFile);
      typeProvider.init(diagram, new ExecutionTreeDiagramEditor());
      assertSame(diagram, typeProvider.getDiagram());
      targets = ExecutionTreeUtil.getAllDebugTargets(typeProvider);
      assertDebugTargets(targets);
      // Test empty linked debug targets
      final ISEDDebugTarget[] expectedTargets = new ISEDDebugTarget[0];
      TransactionalEditingDomain domain = TransactionUtil.getEditingDomain(diagram);
      domain.getCommandStack().execute(new RecordingCommand(domain) {
         @Override
         protected void doExecute() {
            typeProvider.getFeatureProvider().link(diagram, expectedTargets);
         }
      });
      targets = ExecutionTreeUtil.getAllDebugTargets(typeProvider);
      assertDebugTargets(targets);
      // Test one linked debug target
      SEDMemoryDebugTarget firstTarget = new SEDMemoryDebugTarget(null, false);
      final ISEDDebugTarget[] expectedTargetsOne = {firstTarget};
      domain.getCommandStack().execute(new RecordingCommand(domain) {
         @Override
         protected void doExecute() {
            typeProvider.getFeatureProvider().link(diagram, expectedTargetsOne);
         }
      });
      targets = ExecutionTreeUtil.getAllDebugTargets(typeProvider);
      assertDebugTargets(targets, firstTarget);
      // Test two linked debug targets
      SEDMemoryDebugTarget secondTarget = new SEDMemoryDebugTarget(null, false);
      final ISEDDebugTarget[] expectedTargetsTwo = {firstTarget, secondTarget};
      domain.getCommandStack().execute(new RecordingCommand(domain) {
         @Override
         protected void doExecute() {
            typeProvider.getFeatureProvider().link(diagram, expectedTargetsTwo);
         }
      });
      targets = ExecutionTreeUtil.getAllDebugTargets(typeProvider);
      assertDebugTargets(targets, firstTarget, secondTarget);
   }
   
   /**
    * Makes sure that the correct {@link ISEDDebugTarget} are given.
    * @param actualTargets The current {@link ISEDDebugTarget}s.
    * @param expectedTargets The expected {@link ISEDDebugTarget}s.
    * @throws DebugException Occurred Exception.
    */
   protected void assertDebugTargets(ISEDDebugTarget[] actualTargets, ISEDDebugTarget...expectedTargets) throws DebugException {
      assertNotNull(actualTargets);
      assertEquals(actualTargets.length, expectedTargets.length);
      for (int i = 0; i < actualTargets.length; i++) {
         assertSame(actualTargets[i], expectedTargets[i]);
      }
   }

   /**
    * Tests {@link ExecutionTreeUtil#createDomainAndResource(Diagram)}
    */
   @Test
   public void testCreateDomainAndResource() {
      // Test null diagram
      TransactionalEditingDomain domain = ExecutionTreeUtil.createDomainAndResource(null);
      assertNotNull(domain);
      // Test diagram
      Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, "Test", true);
      domain = ExecutionTreeUtil.createDomainAndResource(diagram);
      assertNotNull(domain);
      Resource resource = diagram.eResource();
      assertNotNull(resource);
      // Try to create a domain again
      try {
         ExecutionTreeUtil.createDomainAndResource(diagram);
         fail("Should not be possible.");
      }
      catch (IllegalArgumentException e) {
         assertEquals("The Diagram is already contained in a Resource.", e.getMessage());
         assertSame(resource, diagram.eResource());
      }
   }
   
   /**
    * Tests {@link ExecutionTreeUtil#writeDomainFile(Diagram)}.
    */
   @Test
   public void testWriteDomainFile() throws IOException, CoreException {
      // Test null diagram
      try {
         ExecutionTreeUtil.writeDomainFile(null);
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertEquals("No Diagram defined.", e.getMessage());
      }
      // Test diagram without user defined domain property
      Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, 
                                                                    "Test", 
                                                                    true);
      ResourceSet rst = new ResourceSetImpl();
      Resource resource = rst.createResource(URI.createFileURI("INVALID_FILE"));
      resource.getContents().add(diagram);
      try {
         ExecutionTreeUtil.writeDomainFile(diagram);
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertEquals("Diagram provides no domain model file.", e.getMessage());
      }
      // Test diagram with local file
      File tempFile = File.createTempFile("testReadDomainFile", ".txt");
      tempFile.delete();
      OutputStream out = null;
      try {
         // Create local file
         assertFalse(tempFile.isFile());
         GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, URI.createFileURI(tempFile.getAbsolutePath()).toString());
         out = ExecutionTreeUtil.writeDomainFile(diagram);
         out.write("Local File".getBytes());
         out.close();
         assertEquals("Local File", IOUtil.readFrom(new FileInputStream(tempFile)));
         assertTrue(tempFile.isFile());
         // Modify local file
         out = ExecutionTreeUtil.writeDomainFile(diagram);
         out.write("Local File Changed".getBytes());
         out.close();
         assertEquals("Local File Changed", IOUtil.readFrom(new FileInputStream(tempFile)));
         assertTrue(tempFile.isFile());
         // Test diagram with workspace file
         IProject project = TestUtilsUtil.createProject("ExecutionTreeUtilTest_testWriteDomainFile");
         IFile workspaceFile = project.getFile("Test.txt");
         GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, URI.createPlatformResourceURI(workspaceFile.getFullPath().toString(), true).toString());
         // Create workspace file
         assertFalse(workspaceFile.exists());
         out = ExecutionTreeUtil.writeDomainFile(diagram);
         out.write("Workspace File".getBytes());
         out.close();
         assertEquals("Workspace File", IOUtil.readFrom(workspaceFile.getContents()));
         assertTrue(workspaceFile.exists());
         // Modify workspace file
         out = ExecutionTreeUtil.writeDomainFile(diagram);
         out.write("Workspace File Changed".getBytes());
         out.close();
         assertEquals("Workspace File Changed", IOUtil.readFrom(workspaceFile.getContents()));
         assertTrue(workspaceFile.exists());
      }
      finally {
         if (tempFile != null) {
            tempFile.delete();
         }
         if (out != null) {
            out.close();
         }
      }
   }
   
   /**
    * Tests {@link ExecutionTreeUtil#readDomainFile(org.eclipse.graphiti.mm.pictograms.Diagram)}.
    */
   @Test
   public void testReadDomainFile() throws IOException {
      // Test null diagram
      try {
         ExecutionTreeUtil.readDomainFile(null);
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertEquals("No Diagram defined.", e.getMessage());
      }
      // Test diagram without user defined domain property
      Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, 
                                                                    "Test", 
                                                                    true);
      ResourceSet rst = new ResourceSetImpl();
      Resource resource = rst.createResource(URI.createFileURI("INVALID_FILE"));
      resource.getContents().add(diagram);
      try {
         ExecutionTreeUtil.readDomainFile(diagram);
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertEquals("Diagram provides no domain model file.", e.getMessage());
      }
      // Test diagram with invalid domain property
      GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, "INVALID_URI");
      try {
         ExecutionTreeUtil.readDomainFile(diagram);
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertTrue(e.getMessage().contains("INVALID_URI"));
      }
      // Test diagram with local file
      File tempFile = File.createTempFile("testReadDomainFile", ".txt");
      tempFile.delete();
      InputStream in = null;
      try {
         GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, URI.createFileURI(tempFile.getAbsolutePath()).toString());
         assertFalse(tempFile.isFile());
         try {
            ExecutionTreeUtil.readDomainFile(diagram);
            fail("Should not be possible.");
         }
         catch (IOException e) {
            assertTrue(e.getMessage().contains(tempFile.toString()));
         }
         TestUtilsUtil.createFile(tempFile, "Local File");
         assertTrue(tempFile.isFile());
         in = ExecutionTreeUtil.readDomainFile(diagram);
         assertEquals("Local File", IOUtil.readFrom(in));
         // Test diagram with workspace file
         IProject project = TestUtilsUtil.createProject("ExecutionTreeUtilTest_testReadDomainFile");
         IFile notExistingWorkspaceFile = project.getFile("NotExists.txt");
         GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, URI.createPlatformResourceURI(notExistingWorkspaceFile.getFullPath().toString(), true).toString());
         assertFalse(notExistingWorkspaceFile.exists());
         try {
            ExecutionTreeUtil.readDomainFile(diagram);
            fail("Should not be possible.");
         }
         catch (IOException e) {
            assertTrue(e.getMessage().contains(notExistingWorkspaceFile.getFullPath().toString()));
         }
         IFile workspaceFile = TestUtilsUtil.createFile(project, "Test.txt", "Workspace File");
         assertTrue(workspaceFile.exists());
         GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, URI.createPlatformResourceURI(workspaceFile.getFullPath().toString(), true).toString());
         in = ExecutionTreeUtil.readDomainFile(diagram);
         assertEquals("Workspace File", IOUtil.readFrom(in));
      }
      finally {
         if (tempFile != null) {
            tempFile.delete();
         }
         if (in != null) {
            in.close();
         }
      }
   }
   
   /**
    * Tests {@link ExecutionTreeUtil#getDomainFileURI(Diagram)}.
    */
   @Test
   public void testGetDomainFileURI() throws IOException {
      // Test null diagram
      try {
         ExecutionTreeUtil.getDomainFileURI(null);
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertEquals("No Diagram defined.", e.getMessage());
      }
      // Test diagram without user defined domain property
      Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, 
                                                                    "Test", 
                                                                    true);
      ResourceSet rst = new ResourceSetImpl();
      Resource resource = rst.createResource(URI.createFileURI("INVALID_FILE"));
      resource.getContents().add(diagram);
      try {
         ExecutionTreeUtil.getDomainFileURI(diagram);
         fail("Should not be possible.");
      }
      catch (IOException e) {
         assertEquals("Diagram provides no domain model file.", e.getMessage());
      }
      // Test diagram with valid URI
      URI expectedUri = URI.createFileURI("INVALID.txt");
      GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, expectedUri.toString());
      URI currentUri = ExecutionTreeUtil.getDomainFileURI(diagram);
      assertEquals(expectedUri, currentUri);
   }
   
   /**
    * Tests {@link ExecutionTreeUtil#getInitialDomainFileName(String)}.
    */
   @Test
   public void testGetDomainFile() {
      assertNull(ExecutionTreeUtil.getInitialDomainFileName(null));
      assertEquals("Diagram" + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT, ExecutionTreeUtil.getInitialDomainFileName("Diagram" + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT));
      assertEquals("Diagram" + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT, ExecutionTreeUtil.getInitialDomainFileName("Diagram.txt"));
      assertEquals("Diagram" + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT, ExecutionTreeUtil.getInitialDomainFileName("Diagram"));
   }
}