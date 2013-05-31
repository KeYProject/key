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

package org.key_project.util.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.ui.navigator.resources.ProjectExplorer;
import org.junit.Test;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWT Bot tests for {@link WorkbenchUtil}. 
 * @author Martin Hentschel
 */
public class SWTBotWorkbenchUtilTest extends TestCase {
    /**
     * Tests {@link WorkbenchUtil#selectAndReveal(org.eclipse.core.resources.IResource)}.
     */
    @Test
    public void testSelectAndReveal() {
        // Close intro
        SWTWorkbenchBot bot = new SWTWorkbenchBot();
        TestUtilsUtil.closeWelcomeView(bot);
        // Create test project structure
        final IProject project = TestUtilsUtil.createProject("SWTBotWorkbenchUtilTest_selectAndReveal");
        final IFile file = TestUtilsUtil.createFile(project, "Test.txt", "Hello World!");
        // Open project explorer view
        SWTBotView view = bot.viewById(ProjectExplorer.VIEW_ID);
        final ISelectionProvider provider = view.getReference().getView(true).getViewSite().getSelectionProvider();
        assertNotNull(provider.getSelection());
        assertTrue(provider.getSelection().isEmpty());
        // Select project
        Display.getDefault().syncExec(new Runnable() {
            @Override
            public void run() {
                WorkbenchUtil.selectAndReveal(project);
            }
        });
        bot.waitUntil(TestUtilsUtil.hasSelection(view.bot().tree()));
        assertNotNull(provider.getSelection());
        assertFalse(provider.getSelection().isEmpty());
        assertTrue(provider.getSelection() instanceof IStructuredSelection);
        assertEquals(project, ((IStructuredSelection)provider.getSelection()).toArray()[0]);
        // Unselect everything
        Display.getDefault().syncExec(new Runnable() {
            @Override
            public void run() {
                provider.setSelection(StructuredSelection.EMPTY);
            }
        });
        bot.waitWhile(TestUtilsUtil.hasSelection(view.bot().tree()));
        // Select file
        Display.getDefault().syncExec(new Runnable() {
            @Override
            public void run() {
                WorkbenchUtil.selectAndReveal(file);
            }
        });
        bot.waitUntil(TestUtilsUtil.hasSelection(view.bot().tree()));
        assertNotNull(provider.getSelection());
        assertFalse(provider.getSelection().isEmpty());
        assertTrue(provider.getSelection() instanceof IStructuredSelection);
        assertEquals(file, ((IStructuredSelection)provider.getSelection()).toArray()[0]);
    }
}