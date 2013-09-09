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

package org.key_project.key4eclipse.starter.core.test.testcase;

import java.io.IOException;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.ITextFileBuffer;
import org.eclipse.core.filebuffers.ITextFileBufferManager;
import org.eclipse.core.filebuffers.LocationKind;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.junit.Test;
import org.key_project.key4eclipse.starter.core.test.Activator;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.IRunnableWithDocument;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

/**
 * Tests for {@link KeYUtil}
 * @author Martin Hentschel
 */
public class KeYUtilTest extends AbstractSetupTestCase {
   /**
    * {@link KeYUtil#getSourceLocation(IProject)}
    */
   @Test
   public void testGetSourceLocation() throws Exception {
      // Test null
      try {
         KeYUtil.getSourceLocation(null);
         fail();
      }
      catch (Exception e) {
         assertEquals("Project not defined.", e.getMessage());
      }
      // Test general project
      IProject generalProject = TestUtilsUtil.createProject("KeYUtilTest_testGetSourceLocation_general");
      try {
         KeYUtil.getSourceLocation(generalProject);
         fail();
      }
      catch (Exception e) {
         assertEquals("The project \"" + generalProject.getName() + "\" is no Java project.", e.getMessage());
      }
      // Test java project
      IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeYUtilTest_testGetSourceLocation_java");
      IFolder src = javaProject.getProject().getFolder("src");
      IFolder secondolder = TestUtilsUtil.createFolder(javaProject.getProject(), "secondSrc");
      assertEquals(ResourceUtil.getLocation(src), KeYUtil.getSourceLocation(javaProject.getProject()));
      // Test java project with multiple source paths
      JDTUtil.addClasspathEntry(javaProject, JavaCore.newSourceEntry(secondolder.getFullPath()));
      try {
         KeYUtil.getSourceLocation(javaProject.getProject());
         fail();
      }
      catch (Exception e) {
         assertEquals("Multiple source paths are not supported.", e.getMessage());
      }
   }
   
   /**
    * Tests {@link KeYUtil#getProgramMethod(IMethod, de.uka.ilkd.key.java.JavaInfo)}
    */
   @Test
   public void testGetProgramMethod() throws Exception {
      // Create test project and content
      IJavaProject project = TestUtilsUtil.createJavaProject("KeYUtilTest_testGetProgramMethod");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/jdtMethodToKeYProgramMethodTest", src);
      TestUtilsUtil.waitForBuild();
      // Get JDT method
      IType type = project.findType("JDTMethodToKeYProgramMethodTest");
      IMethod doSomething = type.getMethods()[0];
      assertEquals("doSomething", doSomething.getElementName());
      IType innerType = type.getType("InnerClass");
      assertNotNull(innerType);
      IMethod run = innerType.getMethods()[0];
      assertEquals("run", run.getElementName());
      // Open project in KeY
      KeYEnvironment<?> environment = KeYEnvironment.load(ResourceUtil.getLocation(project.getResource()), null, null);
      try {
         JavaInfo javaInfo = environment.getJavaInfo();
         // Test conversion of doSomething
         IProgramMethod pm = KeYUtil.getProgramMethod(doSomething, javaInfo);
         assertNotNull(pm);
         assertEquals("doSomething", pm.getFullName());
         assertEquals("JDTMethodToKeYProgramMethodTest", pm.getContainerType().getFullName());
         // Test conversion of run
         pm = KeYUtil.getProgramMethod(run, javaInfo);
         assertNotNull(pm);
         assertEquals("run", pm.getFullName());
         assertEquals("JDTMethodToKeYProgramMethodTest.InnerClass", pm.getContainerType().getFullName());
      }
      finally {
         environment.dispose();
      }
   }
   
   /**
    * Tests {@link KeYUtil#getOffsetForCursorPosition(IDocument, int, int, int)} and
    * {@link KeYUtil#getOffsetForCursorPosition(IJavaElement, int, int)}.
    */
   @Test
   public void testGetOffsetForCursorPosition() throws CoreException, InterruptedException {
      // Create test project and content
      IJavaProject project = TestUtilsUtil.createJavaProject("KeYUtilTest_testGetOffsetForCursorPosition");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MCDemo", src);
      TestUtilsUtil.waitForBuild();
      final IMethod method = TestUtilsUtil.getJdtMethod(project, "MCDemo", "init", "I");
      final int tabWidth = JDTUtil.getTabWidth(method);
      // Test all possible offsets
      KeYUtil.runOnDocument(method, new IRunnableWithDocument() {
         @Override
         public void run(IDocument document) throws CoreException {
            try {
               for (int offset = 0; offset < document.getLength(); offset++) {
                  Position cursorPosition = KeYUtil.getCursorPositionForOffset(method, offset);
                  assertNotNull(cursorPosition);
                  assertNotSame(Position.UNDEFINED, cursorPosition);
                  // Test KeYUtil#getOffsetForCursorPosition(IDocument, int, int, int)
                  int cursorOffset = KeYUtil.getOffsetForCursorPosition(document, cursorPosition.getLine(), cursorPosition.getColumn(), tabWidth);
                  assertEquals(offset, cursorOffset);
                  // Test KeYUtil#getOffsetForCursorPosition(IJavaElement, int, int)
                  cursorOffset = KeYUtil.getOffsetForCursorPosition(method, cursorPosition.getLine(), cursorPosition.getColumn());
                  assertEquals(offset, cursorOffset);
               }
            }
            catch (BadLocationException e) {
               throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Test failed.", e));
            }
         }
      });
   }
   
   /**
    * Tests {@link KeYUtil#changeCursorPositionTabWidth(IDocument, Position, int, int)}
    */
   @Test
   public void testChangeCursorPositionTabWidth() throws CoreException, InterruptedException, BadLocationException {
      // Create test project and content
      IJavaProject project = TestUtilsUtil.createJavaProject("KeYUtilTest_testChangeCursorPositionTabWidth");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MCDemo", src);
      TestUtilsUtil.waitForBuild();
      IMethod method = TestUtilsUtil.getJdtMethod(project, "MCDemo", "init", "I");
      // Open document
      DocumentGetterRunnableWithDocument saver = new DocumentGetterRunnableWithDocument();
      KeYUtil.runOnDocument(method, saver);
      IDocument document = saver.getDocument();
      // Test null
      assertSame(Position.UNDEFINED, KeYUtil.changeCursorPositionTabWidth(null, null, JDTUtil.getTabWidth(method), KeYUtil.RECORDER_TAB_SIZE));
      assertSame(Position.UNDEFINED, KeYUtil.changeCursorPositionTabWidth(null, new Position(2, 1), JDTUtil.getTabWidth(method), KeYUtil.RECORDER_TAB_SIZE));
      assertSame(Position.UNDEFINED, KeYUtil.changeCursorPositionTabWidth(document, null, JDTUtil.getTabWidth(method), KeYUtil.RECORDER_TAB_SIZE));
      // Get position
      Position position = KeYUtil.getCursorPositionForOffset(method, method.getSourceRange().getOffset());
      assertNotNull(position);
      assertEquals("17 : 5", position.toString());
      Position converted = KeYUtil.changeCursorPositionTabWidth(document, position, JDTUtil.getTabWidth(method), KeYUtil.RECORDER_TAB_SIZE);
      assertNotNull(converted);
      assertEquals("17 : 9", converted.toString());
   }
   
   /**
    * Tests {@link KeYUtil#getCursorPositionForOffset(IJavaElement, int)}
    */
   @Test
   public void testGetCursorPositionForOffset() throws CoreException, InterruptedException {
      // Create test project and content
      IJavaProject project = TestUtilsUtil.createJavaProject("KeYUtilTest_testGetCursorPositionForOffset");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MCDemo", src);
      TestUtilsUtil.waitForBuild();
      IMethod method = TestUtilsUtil.getJdtMethod(project, "MCDemo", "init", "I");
      // Test null
      assertSame(Position.UNDEFINED, KeYUtil.getCursorPositionForOffset(null, 10));
      // Test invalid offset
      try {
         KeYUtil.getCursorPositionForOffset(method, -4);
         fail("Invalid offset should not be possible.");
      }
      catch (Exception e) {
      }
      // Test valid offsets
      Position position = KeYUtil.getCursorPositionForOffset(method, method.getSourceRange().getOffset());
      assertNotNull(position);
      assertEquals("17 : 5", position.toString());
      position = KeYUtil.getCursorPositionForOffset(method, method.getSourceRange().getOffset() + method.getSourceRange().getLength());
      assertNotNull(position);
      assertEquals("24 : 6", position.toString());
   }
   
   /**
    * Tests {@link KeYUtil#runOnDocument(org.eclipse.jdt.core.IJavaElement, IRunnableWithDocument)}.
    */
   @Test
   public void testRunOnDocument_IJavaElement() throws CoreException, IOException, InterruptedException {
      // Create test project and content
      IJavaProject project = TestUtilsUtil.createJavaProject("KeYUtilTest_testRunOnDocument_IJavaElement");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MCDemo", src);
      TestUtilsUtil.waitForBuild();
      IMethod method = TestUtilsUtil.getJdtMethod(project, "MCDemo", "init", "I");
      // Test null
      assertFalse(KeYUtil.runOnDocument((IJavaElement)null, new DocumentGetterRunnableWithDocument()));
      assertFalse(KeYUtil.runOnDocument(method, null));
      assertFalse(KeYUtil.runOnDocument((IJavaElement)null, null));
      // Test path to valid file which is not opened
      DocumentGetterRunnableWithDocument saver = new DocumentGetterRunnableWithDocument();
      assertTrue(KeYUtil.runOnDocument(method, saver));
      assertNotNull(saver.getDocument());
      assertEquals(IOUtil.readFrom(((IFile)method.getResource()).getContents()), saver.getDocument().get());
   }
   
   /**
    * Tests {@link KeYUtil#runOnDocument(IPath, org.key_project.key4eclipse.starter.core.util.KeYUtil.IRunnableWithDocument)}.
    */
   @Test
   public void testRunOnDocument_IPath() throws CoreException, IOException {
      // Create test project and content
      IProject project = TestUtilsUtil.createProject("KeYUtilTest_testRunOnDocument_Ipath");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MCDemo", project);
      IFile file = project.getFile("MCDemo.java");
      assertTrue(file.exists());
      // Get buffer manager
      ITextFileBufferManager bufferManager = FileBuffers.getTextFileBufferManager();
      assertNotNull(bufferManager);
      // Test null
      assertFalse(KeYUtil.runOnDocument((IPath)null, new DocumentGetterRunnableWithDocument()));
      assertFalse(KeYUtil.runOnDocument(file.getFullPath(), null));
      assertFalse(KeYUtil.runOnDocument((IPath)null, null));
      assertNull(bufferManager.getTextFileBuffer(file.getFullPath(), LocationKind.IFILE));
      // Test path to valid file which is not opened
      DocumentGetterRunnableWithDocument saver = new DocumentGetterRunnableWithDocument();
      assertTrue(KeYUtil.runOnDocument(file.getFullPath(), saver));
      assertNotNull(saver.getDocument());
      assertEquals(IOUtil.readFrom(file.getContents()), saver.getDocument().get());
      assertNull(bufferManager.getTextFileBuffer(file.getFullPath(), LocationKind.IFILE));
      // Test path to not existing file
      saver = new DocumentGetterRunnableWithDocument();
      assertTrue(KeYUtil.runOnDocument(project.getFile("NotExistingFile.txt").getFullPath(), saver));
      assertNotNull(saver.getDocument());
      assertTrue(saver.getDocument().get().isEmpty());
      assertNull(bufferManager.getTextFileBuffer(file.getFullPath(), LocationKind.IFILE));
      // Test path to valid file which is already opened
      try {
         bufferManager.connect(file.getFullPath(), LocationKind.IFILE, null);
         ITextFileBuffer textFileBuffer = bufferManager.getTextFileBuffer(file.getFullPath(), LocationKind.IFILE);
         assertNotNull(textFileBuffer);
         saver = new DocumentGetterRunnableWithDocument();
         assertTrue(KeYUtil.runOnDocument(file.getFullPath(), saver));
         assertNotNull(saver.getDocument());
         assertEquals(IOUtil.readFrom(file.getContents()), saver.getDocument().get());
         assertSame(textFileBuffer, bufferManager.getTextFileBuffer(file.getFullPath(), LocationKind.IFILE));
         assertSame(textFileBuffer, bufferManager.getTextFileBuffer(saver.getDocument()));
      }
      finally {
         bufferManager.disconnect(file.getFullPath(), LocationKind.IFILE, null);
      }
   }
   
   /**
    * Utility class to collect the executed {@link IDocument}.
    * @author Martin Hentschel
    */
   public static class DocumentGetterRunnableWithDocument implements IRunnableWithDocument {
      /**
       * The executed {@link IDocument}.
       */
      private IDocument document;

      /**
       * {@inheritDoc}
       */
      @Override
      public void run(IDocument document) {
         this.document = document;
      }

      /**
       * Returns the executed {@link IDocument}.
       * @return The executed {@link IDocument}.
       */
      public IDocument getDocument() {
         return document;
      }
   }
   
   /**
    * Tests {@link KeYUtil#normalizeRecorderColumn(int, int, int[])} and
    * {@link KeYUtil#normalizeRecorderColumn(int, int[])}.
    */
   @Test
   public void testNormalizeRecorderColumn() {
      // Test invalid parameters
      assertEquals(-1, KeYUtil.normalizeRecorderColumn(-1, 4, new int[] {0}));
      assertEquals(1, KeYUtil.normalizeRecorderColumn(1, 0, new int[] {0}));
      assertEquals(1, KeYUtil.normalizeRecorderColumn(1, 1, new int[] {0}));
      assertEquals(1, KeYUtil.normalizeRecorderColumn(1, 4, null));
      // Test one tab
      doTestNormalizeRecorderColumn("\tABCDEF");
      doTestNormalizeRecorderColumn("A\tBCDEF");
      doTestNormalizeRecorderColumn("AB\tCDEF");
      doTestNormalizeRecorderColumn("ABC\tDEF");
      doTestNormalizeRecorderColumn("ABCD\tEF");
      doTestNormalizeRecorderColumn("ABCDE\tF");
      doTestNormalizeRecorderColumn("ABCDEF\t");
      // Test two tabs
      doTestNormalizeRecorderColumn("\t\tABCDEF");
      doTestNormalizeRecorderColumn("\tA\tBCDEF");
      doTestNormalizeRecorderColumn("\tAB\tCDEF");
      doTestNormalizeRecorderColumn("\tABC\tDEF");
      doTestNormalizeRecorderColumn("\tABCD\tEF");
      doTestNormalizeRecorderColumn("\tABCDE\tF");
      doTestNormalizeRecorderColumn("\tABCDEF\t");
      doTestNormalizeRecorderColumn("A\t\tBCDEF");
      doTestNormalizeRecorderColumn("A\tB\tCDEF");
      doTestNormalizeRecorderColumn("A\tBC\tDEF");
      doTestNormalizeRecorderColumn("A\tBCD\tEF");
      doTestNormalizeRecorderColumn("A\tBCDE\tF");
      doTestNormalizeRecorderColumn("A\tBCDEF\t");
      doTestNormalizeRecorderColumn("AB\t\tCDEF");
      doTestNormalizeRecorderColumn("AB\tC\tDEF");
      doTestNormalizeRecorderColumn("AB\tCD\tEF");
      doTestNormalizeRecorderColumn("AB\tCDE\tF");
      doTestNormalizeRecorderColumn("AB\tCDEF\t");
      doTestNormalizeRecorderColumn("ABC\t\tDEF");
      doTestNormalizeRecorderColumn("ABC\tD\tEF");
      doTestNormalizeRecorderColumn("ABC\tDE\tF");
      doTestNormalizeRecorderColumn("ABC\tDEF\t");
      doTestNormalizeRecorderColumn("ABCD\t\tEF");
      doTestNormalizeRecorderColumn("ABCD\tE\tF");
      doTestNormalizeRecorderColumn("ABCD\tEF\t");
      doTestNormalizeRecorderColumn("ABCDE\t\tF");
      doTestNormalizeRecorderColumn("ABCDE\tF\t");
      doTestNormalizeRecorderColumn("ABCDEF\t\t");
      // Test three tabs
      doTestNormalizeRecorderColumn("\t\t\tABCDEF");
      doTestNormalizeRecorderColumn("A\tBC\tDE\tF");
      doTestNormalizeRecorderColumn("ABC\tD\t\tEF");
      doTestNormalizeRecorderColumn("AB\t\t\tCDEF");
      doTestNormalizeRecorderColumn("ABCDEF\t\t\t");
   }
   
   /**
    * Executes a test case for {@link #testNormalizeColumn()}.
    * @param text The text to test.
    */
   protected void doTestNormalizeRecorderColumn(String text) {
      for (int tabSize = 1; tabSize <= KeYUtil.RECORDER_TAB_SIZE; tabSize++) {
         doTestNormalizeRecorderColumn(text, tabSize);
      }
   }
   
   /**
    * Executes a test case for {@link #testNormalizeColumn()}.
    * @param text The text to test.
    * @param tabSize The tab size to use.
    */
   protected void doTestNormalizeRecorderColumn(String text, int tabSize) {
      assertNotNull(text);
      // Compute tab indices
      int[] tabIndices = new int[0];
      int tabIndex = text.indexOf('\t');
      while (tabIndex >= 0) {
         tabIndices = ArrayUtil.add(tabIndices, tabIndex);
         tabIndex = text.indexOf('\t', tabIndex + 1);
      }
      // Test normalization
      char[] signs = text.toCharArray();
      int column = 0;
      int expectedNoramlizedColumn = 0;
      for (char sign : signs) {
         int actualNormalizedColumn = KeYUtil.normalizeRecorderColumn(column, tabSize, tabIndices);
         assertEquals(expectedNoramlizedColumn, actualNormalizedColumn);
         if (tabSize == KeYUtil.RECORDER_TAB_SIZE) {
            actualNormalizedColumn = KeYUtil.normalizeRecorderColumn(column, tabIndices);
            assertEquals(expectedNoramlizedColumn, actualNormalizedColumn);
         }
         // Update columns
         switch (sign) {
            case '\t' : column += (tabSize - (column % tabSize));
                        break;
            default : column ++;
         }
         expectedNoramlizedColumn ++;
      }
   }
   
   /**
    * Tests {@link KeYUtil#isFileExtensionSupported(String)}.
    */
   @Test
   public void testIsFileExtensionSupported() {
      assertFalse(KeYUtil.isFileExtensionSupported(null));
      assertFalse(KeYUtil.isFileExtensionSupported("INVALID_EXTENSION"));
      assertTrue(KeYUtil.isFileExtensionSupported(KeYUtil.KEY_FILE_EXTENSION));
      assertTrue(KeYUtil.isFileExtensionSupported(KeYUtil.PROOF_FILE_EXTENSION));
   }
}