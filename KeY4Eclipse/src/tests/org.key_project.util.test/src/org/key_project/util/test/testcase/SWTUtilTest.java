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

package org.key_project.util.test.testcase;

import java.io.CharArrayWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.junit.Test;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.ArrayObject;
import org.key_project.util.test.util.ArrayObjectLabelProvider;

/**
 * Contains tests for {@link SWTUtil}.
 * @author Martin Hentschel
 */
public class SWTUtilTest extends TestCase {
   /**
    * Tests {@link SWTUtil#findButtonByText(org.eclipse.swt.widgets.Widget, String)}.
    */
   @Test
   public void testFindButtonByText() {
      Shell shell = new Shell();
      try {
         // Create Buttons
         Button b1shell = new Button(shell, SWT.PUSH);
         b1shell.setText("b1shell");
         Button b2shell = new Button(shell, SWT.RADIO);
         b2shell.setText("b2shell");
         Button b3shell = new Button(shell, SWT.CHECK);
         b3shell.setText("b3shell");
         Composite composite = new Composite(shell, SWT.NONE);
         Button b1composite = new Button(composite, SWT.PUSH);
         b1composite.setText("b1composite");
         Button b2composite = new Button(composite, SWT.RADIO);
         b2composite.setText("b2composite");
         Button b3composite = new Button(composite, SWT.CHECK);
         b3composite.setText("b3composite");
         Composite childCmposite = new Composite(composite, SWT.NONE);
         Button b1childComposite = new Button(childCmposite, SWT.PUSH);
         b1childComposite.setText("b1childComposite");
         Button b2childComposite = new Button(childCmposite, SWT.RADIO);
         b2childComposite.setText("b2childComposite");
         Button b3childComposite = new Button(childCmposite, SWT.CHECK);
         b3childComposite.setText("b3childComposite");
         // Search null
         assertNull(SWTUtil.findButtonByText(shell, null));
         assertNull(SWTUtil.findButtonByText(null, b1shell.getText()));
         assertNull(SWTUtil.findButtonByText(null, null));
         // Search on Shell
         assertNull(SWTUtil.findButtonByText(shell, "INVALID"));
         assertSame(b1shell, SWTUtil.findButtonByText(shell, b1shell.getText()));
         assertSame(b2shell, SWTUtil.findButtonByText(shell, b2shell.getText()));
         assertSame(b3shell, SWTUtil.findButtonByText(shell, b3shell.getText()));
         assertSame(b1composite, SWTUtil.findButtonByText(shell, b1composite.getText()));
         assertSame(b2composite, SWTUtil.findButtonByText(shell, b2composite.getText()));
         assertSame(b3composite, SWTUtil.findButtonByText(shell, b3composite.getText()));
         assertSame(b1childComposite, SWTUtil.findButtonByText(shell, b1childComposite.getText()));
         assertSame(b2childComposite, SWTUtil.findButtonByText(shell, b2childComposite.getText()));
         assertSame(b3childComposite, SWTUtil.findButtonByText(shell, b3childComposite.getText()));
         // Search on Composite
         assertNull(SWTUtil.findButtonByText(composite, "INVALID"));
         assertNull(SWTUtil.findButtonByText(composite, b1shell.getText()));
         assertNull(SWTUtil.findButtonByText(composite, b2shell.getText()));
         assertNull(SWTUtil.findButtonByText(composite, b3shell.getText()));
         assertSame(b1composite, SWTUtil.findButtonByText(composite, b1composite.getText()));
         assertSame(b2composite, SWTUtil.findButtonByText(composite, b2composite.getText()));
         assertSame(b3composite, SWTUtil.findButtonByText(composite, b3composite.getText()));
         assertSame(b1childComposite, SWTUtil.findButtonByText(composite, b1childComposite.getText()));
         assertSame(b2childComposite, SWTUtil.findButtonByText(composite, b2childComposite.getText()));
         assertSame(b3childComposite, SWTUtil.findButtonByText(composite, b3childComposite.getText()));
         // Search on child Composite
         assertNull(SWTUtil.findButtonByText(childCmposite, "INVALID"));
         assertNull(SWTUtil.findButtonByText(childCmposite, b1shell.getText()));
         assertNull(SWTUtil.findButtonByText(childCmposite, b2shell.getText()));
         assertNull(SWTUtil.findButtonByText(childCmposite, b3shell.getText()));
         assertNull(SWTUtil.findButtonByText(childCmposite, b1composite.getText()));
         assertNull(SWTUtil.findButtonByText(childCmposite, b2composite.getText()));
         assertNull(SWTUtil.findButtonByText(childCmposite, b3composite.getText()));
         assertSame(b1childComposite, SWTUtil.findButtonByText(childCmposite, b1childComposite.getText()));
         assertSame(b2childComposite, SWTUtil.findButtonByText(childCmposite, b2childComposite.getText()));
         assertSame(b3childComposite, SWTUtil.findButtonByText(childCmposite, b3childComposite.getText()));
         // Search on Button
         assertNull(SWTUtil.findButtonByText(b1shell, "INVALID"));
         assertSame(b1shell, SWTUtil.findButtonByText(b1shell, b1shell.getText()));
         assertSame(b2shell, SWTUtil.findButtonByText(b2shell, b2shell.getText()));
         assertSame(b3shell, SWTUtil.findButtonByText(b3shell, b3shell.getText()));
      }
      finally {
         shell.dispose();
      }
   }
   
    /**
     * Tests {@link SWTUtil#select(Viewer, org.eclipse.jface.viewers.ISelection, boolean)}
     */
    @Test
    public void testSelect() {
       Shell shell = new Shell();
       try {
          // Create viewer
          String[] input = {"A", "B", "C"};
          shell.setLayout(new FillLayout());
          final ListViewer viewer = new ListViewer(shell);
          viewer.setContentProvider(ArrayContentProvider.getInstance());
          viewer.setInput(input);
          viewer.setSelection(SWTUtil.createSelection("B"));
          assertSelection(viewer.getSelection(), "B");
          // Test null parameters
          SWTUtil.select(null, SWTUtil.createSelection("C"), true);
          assertSelection(viewer.getSelection(), "B");
          SWTUtil.select(viewer, null, true);
          assertSelection(viewer.getSelection());
          SWTUtil.select(null, null, true);
          assertSelection(viewer.getSelection());
          // Change selection in displays thread
          SWTUtil.select(viewer, SWTUtil.createSelection("C"), true);
          assertSelection(viewer.getSelection(), "C");
          // Change selection in different thread
          Job changeJob = new Job("Change Selection") {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
               SWTUtil.select(viewer, SWTUtil.createSelection("A", "B"), true);
               return Status.OK_STATUS;
            }
          };
          changeJob.schedule();
          while (changeJob.getState() != Job.NONE) {
             shell.getDisplay().readAndDispatch();
          }
          assertSelection(viewer.getSelection(), "A", "B");
      }
      finally {
         shell.dispose();
      }
    }
    
    /**
     * Makes sure that the given selection contains the given elements.
     * @param currentSelection The current {@link ISelection}.
     * @param expectedElements The expected contained elements.
     */
    protected void assertSelection(ISelection currentSelection, 
                                   Object... expectedElements) {
       assertTrue(currentSelection instanceof IStructuredSelection);
       Object[] selection = SWTUtil.toArray(currentSelection);
       assertEquals(expectedElements.length, selection.length);
       for (int i = 0; i < expectedElements.length; i++) {
          assertEquals(selection[i], expectedElements[i]);
       }
    }
   
    /**
     * Tests {@link SWTUtil#createSelection(List)}
     */
    @Test
    public void testCreateSelection_Object_List() {
        // Test null and empty
        assertSame(StructuredSelection.EMPTY, SWTUtil.createSelection((List<?>)null));
        assertSame(StructuredSelection.EMPTY, SWTUtil.createSelection(Collections.EMPTY_LIST));
        // Test array with one element
        IStructuredSelection selection = SWTUtil.createSelection(Collections.singletonList("A"));
        assertSelection(selection, "A");
        // Test array with two elements
        selection = SWTUtil.createSelection(CollectionUtil.toList("A", "B"));
        assertSelection(selection, "A", "B");
    }
   
    /**
     * Tests {@link SWTUtil#createSelection(Object[])}
     */
    @Test
    public void testCreateSelection_Object_Array() {
        // Test null and empty
        assertSame(StructuredSelection.EMPTY, SWTUtil.createSelection((Object[])null));
        assertSame(StructuredSelection.EMPTY, SWTUtil.createSelection(new Object[0]));
        // Test array with one element
        IStructuredSelection selection = SWTUtil.createSelection("A");
        assertSelection(selection, "A");
        selection = SWTUtil.createSelection(new Object[] {"A"});
        assertSelection(selection, "A");
        // Test array with two elements
        selection = SWTUtil.createSelection("A", "B");
        assertSelection(selection, "A", "B");
        selection = SWTUtil.createSelection(new Object[] {"A", "B"});
        assertSelection(selection, "A", "B");
    }
   
    /**
     * Tests {@link SWTUtil#createSelection(Object)}
     */
    @Test
    public void testCreateSelection_Object() {
        assertSame(StructuredSelection.EMPTY, SWTUtil.createSelection((Object)null));
        IStructuredSelection selection = SWTUtil.createSelection("A");
        assertSelection(selection, "A");
    }
   
    /**
     * Tests {@link SWTUtil#getFirstElement(ISelection)}
     */
    @Test
    public void testGetFirstElement() {
       assertNull(SWTUtil.getFirstElement(null));
       assertNull(SWTUtil.getFirstElement(StructuredSelection.EMPTY));
       assertEquals("A", SWTUtil.getFirstElement(SWTUtil.createSelection("A")));
       assertEquals("A", SWTUtil.getFirstElement(SWTUtil.createSelection("A", "B")));
    }
   
    /**
     * Tests {@link SWTUtil#toArray(org.eclipse.jface.viewers.ISelection)}
     */
    @Test
    public void testToArray_ISelection() {
        Object[] result = SWTUtil.toArray(null);
        assertNotNull(result);
        assertEquals(0, result.length);
        result = SWTUtil.toArray(StructuredSelection.EMPTY);
        assertNotNull(result);
        assertEquals(0, result.length);
        result = SWTUtil.toArray(SWTUtil.createSelection("A"));
        assertNotNull(result);
        assertEquals(1, result.length);
        assertEquals("A", result[0]);
        result = SWTUtil.toArray(SWTUtil.createSelection("A", "B"));
        assertNotNull(result);
        assertEquals(2, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
    }
   
    /**
     * Tests {@link SWTUtil#toList(org.eclipse.jface.viewers.ISelection)}
     */
    @Test
    public void testToList_ISelection() {
        List<?> result = SWTUtil.toList(null);
        assertNotNull(result);
        assertEquals(0, result.size());
        result = SWTUtil.toList(StructuredSelection.EMPTY);
        assertNotNull(result);
        assertEquals(0, result.size());
        result = SWTUtil.toList(SWTUtil.createSelection("A"));
        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals("A", result.get(0));
        result = SWTUtil.toList(SWTUtil.createSelection("A", "B"));
        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals("A", result.get(0));
        assertEquals("B", result.get(1));
    }
   
    /**
     * Tests {@link SWTUtil#add(Combo, String))}
     */
    @Test
    public void testAdd() {
        // Create UI
        Shell shell = new Shell();
        Combo combo = new Combo(shell, SWT.READ_ONLY);
        // Set "A"
        SWTUtil.add(combo, "A");
        assertEquals("A", combo.getItem(combo.getItemCount() - 1));
        // Set "B"
        SWTUtil.add(combo, "B");
        assertEquals("B", combo.getItem(combo.getItemCount() - 1));
        // Set ""
        SWTUtil.add(combo, "");
        assertEquals("", combo.getItem(combo.getItemCount() - 1));
        // Set "C"
        SWTUtil.add(combo, "C");
        assertEquals("C", combo.getItem(combo.getItemCount() - 1));
        // Set null
        SWTUtil.add(combo, null);
        assertEquals("", combo.getItem(combo.getItemCount() - 1));
    }
   
    /**
     * Tests {@link SWTUtil#csvExport(org.eclipse.swt.widgets.Table)},
     * {@link SWTUtil#csvExport(org.eclipse.swt.widgets.Table, java.io.File)} and
     * {@link SWTUtil#csvExport(org.eclipse.swt.widgets.Table, java.io.Writer)}
     * in a {@link TableViewer} that has no columns.
     */
    @Test
    public void testCsvExport_noColumns() throws IOException {
        // Create model
        List<ArrayObject> input = new LinkedList<ArrayObject>();
        input.add(new ArrayObject("F1", "S1", "T1"));
        input.add(new ArrayObject("F2", "S2", "T2"));
        input.add(new ArrayObject("F3", "S3", "T3"));
        input.add(new ArrayObject("F4", "S4", "T4"));
        // Create UI
        Shell shell = new Shell();
        shell.setLayout(new FillLayout());
        TableViewer viewer = new TableViewer(shell);
        viewer.setContentProvider(ArrayContentProvider.getInstance());
        final ArrayObjectLabelProvider labelProvider = new ArrayObjectLabelProvider();
        viewer.setLabelProvider(labelProvider);
        viewer.setInput(input);
        // Test initial table
        assertCSVContent(viewer, new String[] {"F1"},
                                 new String[] {"F2"},
                                 new String[] {"F3"},
                                 new String[] {"F4"});
        // Test with sorted rows
        viewer.setComparator(new ViewerComparator() {
            @Override
            public int compare(Viewer viewer, Object e1, Object e2) {
                String e1Value = labelProvider.getText(e1);
                String e2Value = labelProvider.getText(e2);
                return e1Value.compareTo(e2Value) * -1;
            }
        });
        assertCSVContent(viewer, new String[] {"F4"},
                                 new String[] {"F3"},
                                 new String[] {"F2"},
                                 new String[] {"F1"});
        // Test with filtered rows
        viewer.addFilter(new ViewerFilter() {
            @Override
            public boolean select(Viewer viewer, Object parentElement, Object element) {
                String value = labelProvider.getColumnText(element, 1);
                return !value.contains("2");
            }
        });
        assertCSVContent(viewer, new String[] {"F4"},
                                 new String[] {"F3"},
                                 new String[] {"F1"});
    }
    
    /**
     * Tests {@link SWTUtil#csvExport(org.eclipse.swt.widgets.Table)},
     * {@link SWTUtil#csvExport(org.eclipse.swt.widgets.Table, java.io.File)} and
     * {@link SWTUtil#csvExport(org.eclipse.swt.widgets.Table, java.io.Writer)}
     * in a {@link TableViewer} that has columns.
     */
    @Test
    public void testCsvExport_withColumns() throws IOException {
        // Create model
        List<ArrayObject> input = new LinkedList<ArrayObject>();
        input.add(new ArrayObject("F1", "S1", "T1"));
        input.add(new ArrayObject("F2", "S2", "T2"));
        input.add(new ArrayObject("F3", "S3", "T3"));
        input.add(new ArrayObject("F4", "S4", "T4"));
        // Create UI
        Shell shell = new Shell();
        shell.setLayout(new FillLayout());
        TableViewer viewer = new TableViewer(shell);
        viewer.getTable().setHeaderVisible(true);
        TableViewerColumn firstColumn = new TableViewerColumn(viewer, SWT.NONE);
        firstColumn.getColumn().setText("First");
        firstColumn.getColumn().setWidth(200);
        TableViewerColumn secondColumn = new TableViewerColumn(viewer, SWT.NONE);
        secondColumn.getColumn().setText("Second");
        secondColumn.getColumn().setWidth(200);
        TableViewerColumn thirdColumn = new TableViewerColumn(viewer, SWT.NONE);
        thirdColumn.getColumn().setText("Third");
        thirdColumn.getColumn().setWidth(200);
        viewer.setContentProvider(ArrayContentProvider.getInstance());
        final ArrayObjectLabelProvider labelProvider = new ArrayObjectLabelProvider();
        viewer.setLabelProvider(labelProvider);
        viewer.setInput(input);
        // Test initial table
        assertCSVContent(viewer, new String[] {"First", "Second", "Third"},
                                 new String[] {"F1", "S1", "T1"},
                                 new String[] {"F2", "S2", "T2"},
                                 new String[] {"F3", "S3", "T3"},
                                 new String[] {"F4", "S4", "T4"});
        // Test with ordered columns
        viewer.getTable().setColumnOrder(new int[] {0, 2, 1});
        assertCSVContent(viewer, new String[] {"First", "Third", "Second"},
                                 new String[] {"F1", "T1", "S1"},
                                 new String[] {"F2", "T2", "S2"},
                                 new String[] {"F3", "T3", "S3"},
                                 new String[] {"F4", "T4", "S4"});
        // Test with sorted rows
        viewer.setComparator(new ViewerComparator() {
            @Override
            public int compare(Viewer viewer, Object e1, Object e2) {
                String e1Value = labelProvider.getColumnText(e1, 1);
                String e2Value = labelProvider.getColumnText(e2, 1);
                return e1Value.compareTo(e2Value) * -1;
            }
        });
        assertCSVContent(viewer, new String[] {"First", "Third", "Second"},
                                 new String[] {"F4", "T4", "S4"},
                                 new String[] {"F3", "T3", "S3"},
                                 new String[] {"F2", "T2", "S2"},
                                 new String[] {"F1", "T1", "S1"});
        // Test with filtered rows
        viewer.addFilter(new ViewerFilter() {
            @Override
            public boolean select(Viewer viewer, Object parentElement, Object element) {
                String value = labelProvider.getColumnText(element, 1);
                return !value.contains("2");
            }
        });
        assertCSVContent(viewer, new String[] {"First", "Third", "Second"},
                                 new String[] {"F4", "T4", "S4"},
                                 new String[] {"F3", "T3", "S3"},
                                 new String[] {"F1", "T1", "S1"});
    }
    
    /**
     * Tests the CSV export of a {@link TableViewer}.
     * @param viewer The {@link TableViewer} that provides the content.
     * @param rows The expected row values.
     * @throws IOException Occurred Exception.
     */
    protected void assertCSVContent(TableViewer viewer,
                                    String[]... rows) throws IOException {
        // Create expected CSV content
        String expectedCsv = createCsv(rows);
        // Create CSV content directly
        String csv = SWTUtil.csvExport(viewer.getTable());
        assertEquals(expectedCsv, csv);
        // Save CSV content to writer
        CharArrayWriter writer = new CharArrayWriter();
        try {
            SWTUtil.csvExport(viewer.getTable(), writer);
            assertEquals(csv, writer.toString());
            writer.close();
        }
        finally {
            if (writer != null) {
                writer.close();
            }
        }
        // Save to file
        File tmpFile = File.createTempFile("SWTUtilTest", ".csv");
        try {
            SWTUtil.csvExport(viewer.getTable(), tmpFile);
            String actualCsv = IOUtil.readFrom(new FileInputStream(tmpFile));
            assertEquals(csv, actualCsv);
        }
        finally {
            if (tmpFile != null) {
                assertTrue(tmpFile.delete());
            }
        }
    }
    
    /**
     * Creates a CSV content for the given values.
     * @param rows The row values.
     * @return The created CSV content.
     */
    protected String createCsv(String[]... rows) {
        StringBuffer sb = new StringBuffer();
        for (String[] row : rows) {
            boolean afterFirst = false;
            for (String value : row) {
                if (afterFirst) {
                    sb.append("; ");
                }
                else {
                    afterFirst = true;
                }
                sb.append(value);
            }
            sb.append(StringUtil.NEW_LINE);
        }
        return sb.toString();
    }

    /**
     * Tests {@link SWTUtil#checkCanceled(org.eclipse.core.runtime.IProgressMonitor)}.
     */
    @Test
    public void testCheckCanceled() {
        SWTUtil.checkCanceled(null); // Monitor is null, nothing should happen
        IProgressMonitor monitor = new NullProgressMonitor();
        SWTUtil.checkCanceled(monitor); // Not canceled, nothing should happen
        monitor.setCanceled(true);
        try {
            SWTUtil.checkCanceled(monitor); // Canceled
            fail("Monitor is canceled, OperationCanceledException expected.");
        }
        catch (OperationCanceledException e) {
            // Everything is fine
        }
    }
    
    /**
     * Tests {@link SWTUtil#setText(org.eclipse.swt.widgets.Text, String)}
     */
    @Test
    public void testSetText_Text() {
        // Create UI
        Shell shell = new Shell();
        Text text = new Text(shell, SWT.BORDER);
        // Set "A"
        SWTUtil.setText(text, "A");
        assertEquals("A", text.getText());
        // Set "B"
        SWTUtil.setText(text, "B");
        assertEquals("B", text.getText());
        // Set ""
        SWTUtil.setText(text, "");
        assertEquals("", text.getText());
        // Set "C"
        SWTUtil.setText(text, "C");
        assertEquals("C", text.getText());
        // Set null
        SWTUtil.setText(text, null);
        assertEquals("", text.getText());
    }
    
    /**
     * Tests {@link SWTUtil#setText(org.eclipse.swt.widgets.Label, String)}
     */
    @Test
    public void testSetText_Label() {
        // Create UI
        Shell shell = new Shell();
        Label label = new Label(shell, SWT.BORDER);
        // Set "A"
        SWTUtil.setText(label, "A");
        assertEquals("A", label.getText());
        // Set "B"
        SWTUtil.setText(label, "B");
        assertEquals("B", label.getText());
        // Set ""
        SWTUtil.setText(label, "");
        assertEquals("", label.getText());
        // Set "C"
        SWTUtil.setText(label, "C");
        assertEquals("C", label.getText());
        // Set null
        SWTUtil.setText(label, null);
        assertEquals("", label.getText());
    }
    
    /**
     * Tests {@link SWTUtil#setText(org.eclipse.swt.widgets.Button, String)}
     */
    @Test
    public void testSetText_Button() {
        // Create UI
        Shell shell = new Shell();
        Button button = new Button(shell, SWT.BORDER);
        // Set "A"
        SWTUtil.setText(button, "A");
        assertEquals("A", button.getText());
        // Set "B"
        SWTUtil.setText(button, "B");
        assertEquals("B", button.getText());
        // Set ""
        SWTUtil.setText(button, "");
        assertEquals("", button.getText());
        // Set "C"
        SWTUtil.setText(button, "C");
        assertEquals("C", button.getText());
        // Set null
        SWTUtil.setText(button, null);
        assertEquals("", button.getText());
    }
}