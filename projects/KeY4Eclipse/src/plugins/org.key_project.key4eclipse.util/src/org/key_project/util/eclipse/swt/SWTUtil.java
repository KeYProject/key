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

package org.key_project.util.eclipse.swt;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;
import org.key_project.util.java.StringUtil;

/**
 * Provides utility methods for SWT.
 * @author Martin Hentschel
 */
public final class SWTUtil {
    /**
     * Separator between CSV values.
     */
    public static final String CSV_VALUE_SEPARATOR = "; ";
   
    /**
     * Forbid instances.
     */
    private SWTUtil() {
    }
    
    /**
     * Checks if the given {@link IProgressMonitor} is canceled.
     * If it is canceled an {@link OperationCanceledException} is thrown.
     * Otherwise nothing happens.
     * @param monitor The {@link IProgressMonitor} to check.
     * @throws OperationCanceledException Thrown exception if the {@link IProgressMonitor} is canceled.
     */
    public static void checkCanceled(IProgressMonitor monitor) throws OperationCanceledException {
        if (monitor != null && monitor.isCanceled()) {
            throw new OperationCanceledException();
        }
    }
    
    /**
     * <p>
     * Configures the given {@link Table} to show only the column {@link Image}s
     * with their real size.
     * </p>
     * <p>
     * It is recommend that not text is set on the {@link TableItem} 
     * (e.g. used {@link LabelProvider} returns no texts) because otherwise
     * it is possible that the cells are to big.
     * </p>
     * @param table The {@link Table} to configure.
     */
    public static void makeTableShowingFullTableItemImages(final Table table) {
        if (table != null) {
            table.addListener(SWT.MeasureItem, new Listener() {
                @Override
                public void handleEvent(Event event) {
                    TableItem item = (TableItem)event.item;
                    event.width = item.getImage().getImageData().width;
                    event.height = item.getImage().getImageData().height;
                }
            });
            table.addListener(SWT.EraseItem, new Listener() {
                public void handleEvent(Event event) {
                    event.detail &= ~SWT.FOREGROUND;
                }
            });
            table.addListener(SWT.PaintItem, new Listener() {
                public void handleEvent(Event event) {
                    TableItem item = (TableItem)event.item;
                    event.gc.drawImage(item.getImage(), event.x >= 0 ? event.x : 0, event.y); // On Linux event.x is negativ what is wrong
                }
            });
        }
    }
    
    /**
     * <p>
     * Configures the given {@link Table} to show multilined text in cells.
     * </p>
     * <p>
     * Example usage
     * <pre><code>
     *   final int TEXT_MARGIN = 3;
     *   Display display = new Display();
     *   Shell shell = new Shell(display);
     *   shell.setLayout(new FillLayout());
     *   final Table table = new Table(shell, SWT.FULL_SELECTION);
     *
     *   TableItem item = new TableItem(table, SWT.NONE);
     *   item.setText("Line1\nLine2");
     *
     *   TableItem item2 = new TableItem(table, SWT.NONE);
     *   item2.setText("1\n2\n3\n4\n5\n6");
     *   
     *   SWTUtil.makeTableMultilined(table, TEXT_MARGIN);
     *
     *   shell.open();
     *   while (!shell.isDisposed()) {
     *           if (!display.readAndDispatch()) display.sleep();
     *   }
     *   display.dispose();
     * </code></pre>
     * </p>
     * <p>
     * The code was copied from SWT Snippet 231.
     * See <a href="http://git.eclipse.org/c/platform/eclipse.platform.swt.git/tree/examples/org.eclipse.swt.snippets/src/org/eclipse/swt/snippets/Snippet231.java">http://git.eclipse.org/c/platform/eclipse.platform.swt.git/tree/examples/org.eclipse.swt.snippets/src/org/eclipse/swt/snippets/Snippet231.java</a>
     * </p>
     * @param table The {@link Table} to configure. If it is {@code null} nothing happens.
     * @param textMargin The text margin to use.
     */
    public static void makeTableMultilined(final Table table, final int textMargin) {
        if (table != null) {
            table.addListener(SWT.MeasureItem, new Listener() {
                public void handleEvent(Event event) {
                    TableItem item = (TableItem)event.item;
                    String text = item.getText(event.index);
                    Point size = event.gc.textExtent(text);
                    event.width = size.x + (2 * textMargin);
                    event.height = Math.max(event.height, size.y + textMargin);
                }
            });
            table.addListener(SWT.EraseItem, new Listener() {
                public void handleEvent(Event event) {
                    event.detail &= ~SWT.FOREGROUND;
                }
            });
            table.addListener(SWT.PaintItem, new Listener() {
                public void handleEvent(Event event) {
                    TableItem item = (TableItem)event.item;
                    String text = item.getText(event.index);
                    int yOffset = 0;
                    event.gc.drawText(text, event.x + textMargin, event.y + yOffset, true);
                }
            });
        }
    }
    
    /**
     * Sets the given text in the given {@link Button} control.
     * @param control The {@link Button} control o set text in.
     * @param text The text to set.
     */
    public static void setText(Button control, String text) {
        if (control != null) {
            control.setText(text != null ? text : StringUtil.EMPTY_STRING);
        }
    }
    
    /**
     * Sets the given text in the given {@link Text} control.
     * @param control The {@link Text} control o set text in.
     * @param text The text to set.
     */
    public static void setText(Text control, String text) {
        if (control != null) {
            control.setText(text != null ? text : StringUtil.EMPTY_STRING);
        }
    }
    
    /**
     * Sets the given text in the given {@link Label} control.
     * @param control The {@link Label} control o set text in.
     * @param text The text to set.
     */
    public static void setText(Label control, String text) {
        if (control != null) {
            control.setText(text != null ? text : StringUtil.EMPTY_STRING);
        }
    }
    
    /**
     * <p>
     * Makes the columns in the given {@link TableViewer} sortable.
     * </p>
     * <p>
     * <b>Attention:</b> It is required to call this method once after
     * the {@link TableViewer} is filled with the available columns.
     * </p>
     * @param viewer The {@link TableViewer} to make his columns sortable.
     */
    public static void makeTableColumnsSortable(final TableViewer viewer) {
        if (viewer != null && !viewer.getTable().isDisposed()) {
            final Table table = viewer.getTable();
            Listener sortListener = new Listener() {
                public void handleEvent(Event e) {
                    // determine new sort column and direction
                    TableColumn sortColumn = table.getSortColumn();
                    TableColumn currentColumn = (TableColumn)e.widget;
                    int dir = table.getSortDirection();
                    if (sortColumn == currentColumn) {
                        if (dir == SWT.UP) {
                            dir = SWT.DOWN;
                        }
                        else if (dir == SWT.DOWN) {
                            dir = SWT.NONE;
                        }
                        else {
                            dir = SWT.UP;
                        }
                    }
                    else {
                        table.setSortColumn(currentColumn);
                        dir = SWT.UP;
                    }
                    table.setSortDirection(dir);
                    final int columnIndex = table.indexOf(currentColumn);
                    final int sortDirection = dir;
                    // sort the data based on column and direction
                    viewer.setComparator(new ViewerComparator() {
                        @Override
                        public int compare(Viewer viewerComp, Object e1, Object e2) {
                            if (sortDirection == SWT.UP || sortDirection == SWT.DOWN) {
                                Assert.isTrue(viewer.getLabelProvider() instanceof ITableLabelProvider);
                                ITableLabelProvider provider = (ITableLabelProvider)viewer.getLabelProvider();
                                String e1value = provider.getColumnText(e1, columnIndex);
                                String e2value = provider.getColumnText(e2, columnIndex);
                                int comparison = e1value.compareTo(e2value);
                                if (sortDirection == SWT.UP) {
                                    return comparison;
                                }
                                else {
                                    return comparison * -1;
                                }
                            }
                            else {
                                return 0; // Original order.
                            }
                        }
                    });
                }
            };
            TableColumn[] columns = table.getColumns();
            for (TableColumn column : columns) {
                column.addListener(SWT.Selection, sortListener);
            }
        }
    }

    /**
     * Exports the content from the given {@link Table} as CSV file.
     * @param table The {@link Table} to export.
     * @param file The file to store the CSV content in.
     * @throws IOException Occurred Exception.
     */
    public static void csvExport(Table table, File file) throws IOException {
        if (table != null && file != null) {
            FileWriter out = null;
            try {
                out = new FileWriter(file);
                csvExport(table, out);
            }
            finally {
                if (out != null) {
                    out.close();
                }
            }
        }
    }

    /**
     * Exports the content from the given {@link Table} as CSV file.
     * @param table The {@link Table} to export.
     * @param writer The {@link Writer} to store the CSV content in.
     * @throws IOException Occurred Exception.
     */
    public static void csvExport(Table table, Writer writer) throws IOException {
        if (table != null && writer != null) {
            String content = csvExport(table);
            writer.write(content);
        }
    }

    /**
     * Exports the content from the given {@link Table} as CSV file.
     * @param table The {@link Table} to export.
     * @return The created CSV content.
     */
    public static String csvExport(Table table) {
        StringBuffer sb = new StringBuffer();
        if (table != null && !table.isDisposed()) {
            // Append columns if possible
            int numOfColumns = table.getColumnCount();
            int[] columnOrder = table.getColumnOrder();
            if (numOfColumns >= 1) {
                TableColumn[] columns = table.getColumns();
                boolean afterFirst = false;
                for (int index : columnOrder) {
                    if (afterFirst) {
                        sb.append(CSV_VALUE_SEPARATOR);
                    }
                    else {
                        afterFirst = true;
                    }
                    sb.append(columns[index].getText());
                }
                sb.append(StringUtil.NEW_LINE);
            }
            // Append rows
            TableItem[] items = table.getItems();
            for (TableItem item : items) {
                if (numOfColumns >= 1) {
                    boolean afterFirst = false;
                    for (int index : columnOrder) {
                        if (afterFirst) {
                            sb.append(CSV_VALUE_SEPARATOR);
                        }
                        else {
                            afterFirst = true;
                        }
                        sb.append(item.getText(index));
                    }
                }
                else {
                    sb.append(item.getText());
                }
                sb.append(StringUtil.NEW_LINE);
            }
        }
        return sb.toString();
    }

    /**
     * Adds the given text as item to the given {@link Combo}.
     * @param control The {@link Combo} to add the item to.
     * @param text The item to add.
     */
    public static void add(Combo control, String text) {
        if (control != null) {
            control.add(text != null ? text : StringUtil.EMPTY_STRING);
        }
    }

    /**
     * Returns the first element from the given {@link ISelection} if
     * it is an {@link IStructuredSelection}.
     * @param selection The {@link ISelection} to read from.
     * @return The first selected element in the given {@link ISelection}.
     */
    public static Object getFirstElement(ISelection selection) {
        if (selection instanceof IStructuredSelection) {
            return ((IStructuredSelection)selection).getFirstElement();
        }
        else {
            return null;
        }
    }

    /**
     * Converts the given {@link ISelection} into an array if it is an
     * {@link IStructuredSelection}.
     * @param selection The {@link ISelection} to convert.
     * @return The selected elements in the given {@link ISelection} as array.
     */
    public static Object[] toArray(ISelection selection) {
        if (selection instanceof IStructuredSelection) {
            return ((IStructuredSelection)selection).toArray();
        }
        else {
            return new Object[0];
        }
    }

    /**
     * Converts the given {@link ISelection} into a {@link List} if it is an
     * {@link IStructuredSelection}.
     * @param selection The {@link ISelection} to convert.
     * @return The selected elements in the given {@link ISelection} as {@link List}.
     */
    public static List<?> toList(ISelection selection) {
        if (selection instanceof IStructuredSelection) {
            return ((IStructuredSelection)selection).toList();
        }
        else {
            return Collections.EMPTY_LIST;
        }
    }

    /**
     * Creates an {@link IStructuredSelection} for the given {@link Object}.
     * @param obj The given {@link Object}.
     * @return The {@link IStructuredSelection} which contains the given {@link Object}.
     */
    public static IStructuredSelection createSelection(Object obj) {
        if (obj != null) {
            return new StructuredSelection(obj);
        }
        else {
            return StructuredSelection.EMPTY;
        }
    }

    /**
     * Creates an {@link IStructuredSelection} for the given {@link Object}s.
     * @param objs The given {@link Object}s.
     * @return The {@link IStructuredSelection} which contains the given {@link Object}.
     */
    public static IStructuredSelection createSelection(Object... objs) {
        if (objs != null && objs.length >= 1) {
            return new StructuredSelection(objs);
        }
        else {
            return StructuredSelection.EMPTY;
        }
    }

    /**
     * Creates an {@link IStructuredSelection} for the given {@link Object}s.
     * @param objs The given {@link Object}s.
     * @return The {@link IStructuredSelection} which contains the given {@link Object}.
     */
    public static IStructuredSelection createSelection(List<?> objs) {
        if (objs != null && !objs.isEmpty()) {
            return new StructuredSelection(objs);
        }
        else {
            return StructuredSelection.EMPTY;
        }
    }
    
    /**
     * Thread save execution of {@link Viewer#setSelection(ISelection, boolean)}.
     * @param viewer The {@link Viewer} to change selection.
     * @param selection The new selection to set.
     * @param reveal {@code true} if the selection is to be made visible, and {@code false} otherwise.
     */
    public static void select(final Viewer viewer, 
                              final ISelection selection, 
                              final boolean reveal) {
       if (viewer != null && !viewer.getControl().isDisposed()) {
          viewer.getControl().getDisplay().syncExec(new Runnable() {
             @Override
             public void run() {
                viewer.setSelection(selection, reveal);
             }
          });
       }
    }
}