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

import java.util.List;

import junit.framework.TestCase;

import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.IContentProvider;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotLabel;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.junit.Test;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.dialog.ElementTableSelectionDialog;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.test.util.ArrayObject;
import org.key_project.util.test.util.ArrayObjectLabelProvider;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWT Bot tests for {@link ElementTableSelectionDialog}. 
 * @author Martin Hentschel
 */
public class SWTBotTableSelectionDialogTest extends TestCase {
    /**
     * Opens the dialog with single selection.
     */
    @Test
    public void testMultiSelectionResult() {
        // Create model
        ArrayObject o1 = new ArrayObject("o1");
        ArrayObject o2 = new ArrayObject("o2");
        ArrayObject o3 = new ArrayObject("o3");
        ArrayObject o4 = new ArrayObject("o4");
        final List<ArrayObject> input = CollectionUtil.toList(o1, o2, o3, o4);
        // Get active shell
        IRunnableWithResult<Shell> shellRun = new AbstractRunnableWithResult<Shell>() {
            @Override
            public void run() {
                setResult(WorkbenchUtil.getActiveShell());
            }
        };
        Display.getDefault().syncExec(shellRun);
        // Create dialog
        Shell parent = shellRun.getResult();
        IContentProvider contentProvider = ArrayContentProvider.getInstance();
        ILabelProvider labelProvider = new ArrayObjectLabelProvider();
        ElementTableSelectionDialog dialog = new ElementTableSelectionDialog(parent, contentProvider, labelProvider);
        dialog.setTitle("SWTBotTableSelectionDialogTest_testMultiSelectionResult");
        dialog.setInput(input);
        dialog.setAllowMultiple(true);
        // Open dialog again and approve it
        dialog.setMessage("testSignleSelectionResult 1");
        openDialog(dialog, "SWTBotTableSelectionDialogTest_testMultiSelectionResult", "testSignleSelectionResult 1", new int[] {1}, ElementTableSelectionDialog.OK, o2);
        // Open dialog and cancel it
        dialog.setMessage("testSignleSelectionResult 2");
        openDialog(dialog, "SWTBotTableSelectionDialogTest_testMultiSelectionResult", "testSignleSelectionResult 2", new int[] {1}, ElementTableSelectionDialog.CANCEL);
        // Open dialog with multiple selections and approve it
        dialog.setMessage("testSignleSelectionResult 3");
        openDialog(dialog, "SWTBotTableSelectionDialogTest_testMultiSelectionResult", "testSignleSelectionResult 3", new int[] {1, 3}, ElementTableSelectionDialog.OK, o2, o4);
        // Open dialog with multiple selections and cancel it
        dialog.setMessage("testSignleSelectionResult 4");
        openDialog(dialog, "SWTBotTableSelectionDialogTest_testMultiSelectionResult", "testSignleSelectionResult 4", new int[] {1, 3}, ElementTableSelectionDialog.CANCEL);
    }
    
    /**
     * Opens the dialog with single selection.
     */
    @Test
    public void testSignleSelectionResult() {
        // Create model
        ArrayObject o1 = new ArrayObject("o1");
        ArrayObject o2 = new ArrayObject("o2");
        ArrayObject o3 = new ArrayObject("o3");
        ArrayObject o4 = new ArrayObject("o4");
        final List<ArrayObject> input = CollectionUtil.toList(o1, o2, o3, o4);
        // Get active shell
        IRunnableWithResult<Shell> shellRun = new AbstractRunnableWithResult<Shell>() {
            @Override
            public void run() {
                setResult(WorkbenchUtil.getActiveShell());
            }
        };
        Display.getDefault().syncExec(shellRun);
        // Create dialog
        Shell parent = shellRun.getResult();
        IContentProvider contentProvider = ArrayContentProvider.getInstance();
        ILabelProvider labelProvider = new ArrayObjectLabelProvider();
        ElementTableSelectionDialog dialog = new ElementTableSelectionDialog(parent, contentProvider, labelProvider);
        dialog.setTitle("SWTBotTableSelectionDialogTest_testSignleSelectionResult");
        dialog.setInput(input);
        // Open dialog again and approve it
        dialog.setMessage("testSignleSelectionResult 1");
        openDialog(dialog, "SWTBotTableSelectionDialogTest_testSignleSelectionResult", "testSignleSelectionResult 1", new int[] {1}, ElementTableSelectionDialog.OK, o2);
        // Open dialog and cancel it
        dialog.setMessage("testSignleSelectionResult 2");
        openDialog(dialog, "SWTBotTableSelectionDialogTest_testSignleSelectionResult", "testSignleSelectionResult 2", new int[] {1}, ElementTableSelectionDialog.CANCEL);
        // Make sure that multiple selections are not possible
        try {
            dialog.setMessage("testSignleSelectionResult 3");
            openDialog(dialog, "SWTBotTableSelectionDialogTest_testSignleSelectionResult", "testSignleSelectionResult 3", new int[] {1, 2}, ElementTableSelectionDialog.OK);
        }
        catch (IllegalArgumentException e) {
            assertEquals("Table does not support multi selection.", e.getMessage());
        }
    }
    
    /**
     * Opens the given {@link ElementTableSelectionDialog} and makes sure
     * that the correct result is returned.
     * @param dialog The {@link ElementTableSelectionDialog} to open.
     * @param dialogTitle The dialog title to use.
     * @param dialogMessage The expected dialog message.
     * @param indicesToSelect The rows to select.
     * @param expectedDialogResult The expected dialog result.
     * @param expectedSelection The expected selection.
     */
    protected void openDialog(final ElementTableSelectionDialog dialog,
                              String dialogTitle,
                              String dialogMessage,
                              int[] indicesToSelect,
                              int expectedDialogResult,
                              Object... expectedSelection) {
        SWTBotShell shell = null;
        try {
            // Open dialog
            IRunnableWithResult<Integer> run = new AbstractRunnableWithResult<Integer>() {
                @Override
                public void run() {
                    setResult(dialog.open());
                }
            };
            Display.getDefault().asyncExec(run);
            // Get dialog
            SWTBot bot = new SWTBot();
            shell = bot.shell(dialogTitle);
            // Test label
            SWTBotLabel label = shell.bot().label(dialogMessage);
            assertEquals(dialogMessage, label.getText());
            // Make sure that the correct values are shown
            SWTBotTable table = shell.bot().table();
            TestUtilsUtil.assertTableRows(table, "o1", "o2", "o3", "o4");
            // Select second item
            table.select(indicesToSelect);
            // Approve dialog
            SWTBotButton button = shell.bot().button(ElementTableSelectionDialog.OK == expectedDialogResult ? "OK" : "Cancel");
            button.click();
            assertFalse(shell.isOpen());
            Integer dialogResult = run.getResult();
            assertNotNull(dialogResult);
            assertEquals(expectedDialogResult, dialogResult.intValue());
            if (expectedSelection.length >= 1) {
                assertEquals(expectedSelection[0], dialog.getFirstResult());
            }
            else {
                assertNull(dialog.getFirstResult());
            }
            assertNotNull(dialog.getResult());
            assertEquals(expectedSelection.length, dialog.getResult().length);
            for (int i = 0; i < expectedSelection.length; i++) {
                assertEquals(expectedSelection[i], dialog.getResult()[i]);
            }
        }
        finally {
            if (shell != null && shell.isOpen()) {
                shell.close();
            }
        }
    }
}