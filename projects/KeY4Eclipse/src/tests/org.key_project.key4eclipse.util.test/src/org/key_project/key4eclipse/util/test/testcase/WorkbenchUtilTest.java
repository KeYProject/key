package org.key_project.key4eclipse.util.test.testcase;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.junit.Test;
import org.key_project.key4eclipse.util.eclipse.WorkbenchUtil;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil;

/**
 * Contains tests for {@link WorkbenchUtil}.
 * @author Martin Hentschel
 */
public class WorkbenchUtilTest extends TestCase {
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
