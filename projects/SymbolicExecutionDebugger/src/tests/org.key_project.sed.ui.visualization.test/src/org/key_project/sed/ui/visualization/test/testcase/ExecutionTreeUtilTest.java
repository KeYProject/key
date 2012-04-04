package org.key_project.sed.ui.visualization.test.testcase;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.junit.Test;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link ExecutionTreeUtil}
 * @author Martin Hentschel
 */
public class ExecutionTreeUtilTest extends TestCase {
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
