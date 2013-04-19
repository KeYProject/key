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

package org.key_project.util.test.testcase;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.navigator.resources.ProjectExplorer;
import org.junit.Test;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.test.perspective.EmptyTestPerspectiveFactory;
import org.key_project.util.test.util.TestUtilsUtil;
import org.key_project.util.test.view.GraphitiEditorInViewView;

/**
 * Contains tests for {@link WorkbenchUtil}.
 * @author Martin Hentschel
 */
public class WorkbenchUtilTest extends TestCase {
   /**
    * Tests {@link WorkbenchUtil#getPerspectiveName(String)}.
    */
   @Test
   public void testGetPerspectiveName() {
      assertNull(WorkbenchUtil.getPerspectiveName("invalid"));
      assertEquals("Empty Test Perspective", WorkbenchUtil.getPerspectiveName(EmptyTestPerspectiveFactory.PERSPECTIVE_ID));
   }
   
   /**
    * Tests {@link WorkbenchUtil#openPerspective(String)},
    * {@link WorkbenchUtil#closePerspective(IPerspectiveDescriptor, boolean, boolean)} and
    * {@link WorkbenchUtil#isPerspectiveOpen(String, IWorkbenchPage)}.
    */
   @Test
   public void testOpenCloseAndIsOpenPerspective() {
      IWorkbenchPage activePage = WorkbenchUtil.getActivePage();
      IPerspectiveDescriptor oldPerspective = activePage.getPerspective();
      assertFalse(WorkbenchUtil.isPerspectiveOpen(EmptyTestPerspectiveFactory.PERSPECTIVE_ID, activePage));
      IPerspectiveDescriptor newPerspective = WorkbenchUtil.openPerspective(EmptyTestPerspectiveFactory.PERSPECTIVE_ID);
      assertTrue(WorkbenchUtil.isPerspectiveOpen(EmptyTestPerspectiveFactory.PERSPECTIVE_ID, activePage));
      assertFalse(WorkbenchUtil.isPerspectiveOpen(EmptyTestPerspectiveFactory.PERSPECTIVE_ID, null));
      assertFalse(WorkbenchUtil.isPerspectiveOpen(null, activePage));
      assertNotNull(newPerspective);
      assertEquals(EmptyTestPerspectiveFactory.PERSPECTIVE_ID, newPerspective.getId());
      assertEquals(newPerspective, activePage.getPerspective());
      WorkbenchUtil.closePerspective(newPerspective, false, false);
      assertFalse(WorkbenchUtil.isPerspectiveOpen(EmptyTestPerspectiveFactory.PERSPECTIVE_ID, activePage));
      assertEquals(oldPerspective, activePage.getPerspective());
      WorkbenchUtil.closePerspective(null, false, false);
      assertEquals(oldPerspective, activePage.getPerspective());
   }
   
    /**
     * Tests {@link WorkbenchUtil#openView(String)},
     * {@link WorkbenchUtil#findView(String)},
     * {@link WorkbenchUtil#isActive(IWorkbenchPart)},
     * {@link WorkbenchUtil#activate(IWorkbenchPart)} and
     * {@link WorkbenchUtil#closeView(IViewPart)}.
     */
    @Test
    public void testViewManagement() throws PartInitException {
       // Make sure that view is not open
       String viewId = GraphitiEditorInViewView.VIEW_ID;
       IViewPart view = WorkbenchUtil.findView(viewId);
       assertNull(view);
       IViewPart explorer = WorkbenchUtil.findView(ProjectExplorer.VIEW_ID);
       assertNotNull(explorer);
       // Open view
       view = WorkbenchUtil.openView(viewId);
       assertNotNull(view);
       assertEquals(viewId, view.getViewSite().getId());
       assertTrue(WorkbenchUtil.isActive(view));
       assertFalse(WorkbenchUtil.isActive(explorer));
       // Select project explorer view
       WorkbenchUtil.activate(explorer);
       assertFalse(WorkbenchUtil.isActive(view));
       assertTrue(WorkbenchUtil.isActive(explorer));
       // Open view again
       IViewPart reopenedView = WorkbenchUtil.openView(viewId);
       assertNotNull(reopenedView);
       assertSame(view, reopenedView);
       assertTrue(WorkbenchUtil.isActive(view));
       assertTrue(WorkbenchUtil.isActive(reopenedView));
       assertFalse(WorkbenchUtil.isActive(explorer));
       // Close view
       WorkbenchUtil.closeView(view);
       assertFalse(WorkbenchUtil.isActive(view));
       assertFalse(WorkbenchUtil.isActive(reopenedView));
       // Search view again
       IViewPart closedView = WorkbenchUtil.findView(viewId);
       assertNull(closedView);
       // Search explorer again
       IViewPart explorerAgain = WorkbenchUtil.findView(ProjectExplorer.VIEW_ID);
       assertNotNull(explorerAgain);
       assertSame(explorer, explorerAgain);
    }

    /**
     * Tests {@link WorkbenchUtil#getActiveShell()}
     */
    @Test
    public void testGetActiveShell() {
        assertNotNull(WorkbenchUtil.getActiveShell());
    }

    /**
     * Tests {@link WorkbenchUtil#getActiveEditor()}
     */
    @Test
    public void testGetActiveEditor() throws PartInitException {
        IEditorPart editor = null;
        try {
            // Make sure that no editor is opened
            assertNull(WorkbenchUtil.getActiveEditor());
            // Create project and file
            IProject project = TestUtilsUtil.createProject("WorkbenchUtilTest_testGetActiveEditor");
            IFile file = TestUtilsUtil.createFile(project, "Test.txt", "Hello World");
            // Open editor
            editor = WorkbenchUtil.openEditor(file);
            // Make sure that editor is opened
            IEditorPart active = WorkbenchUtil.getActiveEditor();
            assertNotNull(active);
            assertEquals(editor, active);
            assertSame(active, WorkbenchUtil.getActivePart());
            // Close editor
            WorkbenchUtil.closeEditor(editor, true);
            // Make sure that no editor is opened
            assertNull(WorkbenchUtil.getActiveEditor());
            assertNotSame(active, WorkbenchUtil.getActivePart());
        }
        finally {
            WorkbenchUtil.closeEditor(editor, true);
        }
    }

    /**
     * Tests {@link WorkbenchUtil#getActivePart()}
     */
    @Test
    public void testGetActivePart() throws PartInitException {
       IWorkbenchPart part = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActivePart();
       assertEquals(part, WorkbenchUtil.getActivePart());
    }

    /**
     * Tests {@link WorkbenchUtil#getActivePage()}
     */
    @Test
    public void testGetActivePage() {
        assertNotNull(WorkbenchUtil.getActivePage());
    }

    /**
     * Tests {@link WorkbenchUtil#getActiveWorkbenchWindow()}
     */
    @Test
    public void testGetActiveWorkbenchWindow() {
        assertNotNull(WorkbenchUtil.getActiveWorkbenchWindow());
    }
    
    /**
     * Tests {@link WorkbenchUtil#openEditor(org.eclipse.core.resources.IFile)}
     * and {@link WorkbenchUtil#closeEditor(IEditorPart, boolean)}
     */
    @Test
    public void testOpenAndCloseEditor() throws PartInitException {
        // Test opening and closing an editor.
        IProject project = TestUtilsUtil.createProject("WorkbenchUtilTest_testOpenAndCloseEditor");
        IFile file = TestUtilsUtil.createFile(project, "Test.txt", "Hello World!");
        IEditorPart editor = WorkbenchUtil.openEditor(file);
        assertNotNull(editor);
        assertNotNull(editor.getEditorInput());
        assertEquals(file, editor.getEditorInput().getAdapter(IFile.class));
        assertTrue(editor.getEditorSite().getPage().isPartVisible(editor));
        boolean closed = WorkbenchUtil.closeEditor(editor, true);
        assertTrue(closed);
        assertFalse(editor.getEditorSite().getPage().isPartVisible(editor));
        // Try to close already closed editor again
        closed = WorkbenchUtil.closeEditor(editor, true);
        assertTrue(closed);
        assertFalse(editor.getEditorSite().getPage().isPartVisible(editor));
        // Test opening null parameter
        try {
            WorkbenchUtil.openEditor(null);
            fail("Opening null should not be possible.");
        }
        catch (Exception e) {
            assertEquals("No file to open defined.", e.getMessage());
        }
        // Test closing null parameter
        closed = WorkbenchUtil.closeEditor(null, true);
        assertTrue(closed);
    }
}