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

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.ide.IDE;
import org.key_project.key4eclipse.starter.core.expression.JavaTextSelectionPropertyTester;
import org.key_project.key4eclipse.starter.core.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link JavaTextSelectionPropertyTester}.
 * @author Martin Hentschel
 */
public class JavaTextSelectionPropertyTesterTest extends TestCase {
    /**
     * Tests {@link JavaTextSelectionPropertyTester#test(Object, String, Object[], Object)}.
     */
    public void testTest_selectedElementInstanceOf() throws CoreException, InterruptedException {
        IEditorPart editor = null;
        try {
            // Create test project
            IJavaProject javaProject = TestUtilsUtil.createJavaProject("JavaTextSelectionPropertyTesterTest_testTest_selectedElementInstanceOf");
            IFolder banking = javaProject.getProject().getFolder("src").getFolder("banking");
            if (!banking.exists()) {
                banking.create(true, true, null);
            }
            BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
            IFile paycardFile = banking.getFile("PayCard.java");
            // Open Java editor
            editor = WorkbenchUtil.openEditor(paycardFile);
            // Select method
            ISelection selection = new TextSelection(216, 6); // Select method charge
            editor.getSite().getSelectionProvider().setSelection(selection);
            // Test method in selection
            JavaTextSelectionPropertyTester tester = new JavaTextSelectionPropertyTester();
            assertTrue(tester.test(editor.getSite().getSelectionProvider().getSelection(), "selectedElementInstanceOf", null, IMethod.class.getCanonicalName()));
            assertTrue(tester.test(editor, "selectedElementInstanceOf", null, IMethod.class.getCanonicalName()));
            // Select attribute
            selection = new TextSelection(77, 7); // Select attribute
            editor.getSite().getSelectionProvider().setSelection(selection);
            // Test attribute in selection
            assertFalse(tester.test(editor.getSite().getSelectionProvider().getSelection(), "selectedElementInstanceOf", null, IMethod.class.getCanonicalName()));
            assertFalse(tester.test(editor, "selectedElementInstanceOf", null, IMethod.class.getCanonicalName()));
            // Close editor
            WorkbenchUtil.closeEditor(editor, true);
            // Test no editor opened
            assertFalse(tester.test(selection, "selectedElementInstanceOf", null, IMethod.class.getCanonicalName()));
            // Test with wrong editor (Simple text editor)
            editor = IDE.openEditor(WorkbenchUtil.getActivePage(), paycardFile, WorkbenchUtil.DEFAULT_TEXT_EDITOR_ID);
            // Select method
            selection = new TextSelection(216, 6); // Select method charge
            editor.getSite().getSelectionProvider().setSelection(selection);
            // Test method in selection
            assertFalse(tester.test(editor.getSite().getSelectionProvider().getSelection(), "selectedElementInstanceOf", null, IMethod.class.getCanonicalName()));
            assertFalse(tester.test(editor, "selectedElementInstanceOf", null, IMethod.class.getCanonicalName()));
        }
        finally {
            WorkbenchUtil.closeEditor(editor, true);
        }
    }
}