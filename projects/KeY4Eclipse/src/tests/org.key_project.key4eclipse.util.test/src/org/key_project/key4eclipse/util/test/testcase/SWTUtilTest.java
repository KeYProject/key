package org.key_project.key4eclipse.util.test.testcase;

import java.io.CharArrayWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.junit.Test;
import org.key_project.key4eclipse.util.eclipse.swt.SWTUtil;
import org.key_project.key4eclipse.util.java.IOUtil;
import org.key_project.key4eclipse.util.java.StringUtil;
import org.key_project.key4eclipse.util.test.util.ArrayObject;
import org.key_project.key4eclipse.util.test.util.ArrayObjectLabelProvider;

/**
 * Contains tests for {@link SWTUtil}.
 * @author Martin Hentschel
 */
public class SWTUtilTest extends TestCase {
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
        viewer.setContentProvider(new ArrayContentProvider());
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
        viewer.setContentProvider(new ArrayContentProvider());
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
    public void testSetText() {
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
}
