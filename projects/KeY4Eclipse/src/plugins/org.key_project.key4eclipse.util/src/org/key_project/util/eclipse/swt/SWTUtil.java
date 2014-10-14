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
import org.eclipse.jface.viewers.AbstractTableViewer;
import org.eclipse.jface.viewers.AbstractTreeViewer;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.VerifyEvent;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Item;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.Widget;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

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
    
    /**
     * Thread save execution of {@link TreeViewer#expandToLevel(Object, int)}.
     * @param viewer The {@link TreeViewer} to expand element in.
     * @param elementOrTreePaths The element to expand.
     * @param level Non-negative level, or {@link AbstractTreeViewer#ALL_LEVELS} to expand all levels of the tree.
     */
    public static void expandToLevel(final TreeViewer viewer, 
                                     final Object elementOrTreePath,
                                     final int level) {
       if (viewer != null && !viewer.getControl().isDisposed()) {
          viewer.getControl().getDisplay().syncExec(new Runnable() {
             @Override
             public void run() {
                viewer.expandToLevel(elementOrTreePath, level);
             }
          });
       }
    }
    
    /**
     * Returns the new text which will be shown if {@link VerifyEvent#doit} is {@code true}.
     * @param e The {@link VerifyEvent}.
     * @return The new text.
     */
    public static String getNewText(VerifyEvent e) {
       if (e.getSource() instanceof Text) {
          String oldText = ((Text)e.widget).getText();
          StringBuilder sb = new StringBuilder();
          sb.append(oldText.substring(0, e.start));
          sb.append(e.text);
          sb.append(oldText.substring(e.end));
          return sb.toString();
       }
       else {
          throw new IllegalArgumentException("Widgets of type \"" + e.getSource().getClass() + " \" are not supported.");
       }
    }

   /**
    * Searches a {@link Button} with the given text in the given {@link Widget}.
    * @param widget The {@link Widget} to search in.
    * @param text The text of the {@link Button} to search.
    * @return The found {@link Button} or {@code null} if no {@link Button} with that text is available.
    */
   public static Button findButtonByText(Widget widget, String text) {
      Button result = null;
      if (widget instanceof Button) {
         Button button = (Button)widget;
         if (button.getText().equals(text)) {
            result = button;
         }
      }
      else if (widget instanceof Composite) {
         Composite composite = (Composite)widget;
         Control[] children = composite.getChildren();
         int i = 0;
         while (result == null && i < children.length) {
            result = findButtonByText(children[i], text);
            i++;
         }
      }
      return result;
   }

   /**
    * Invokes {@link Viewer#refresh()} thread save.
    * @param viewer The {@link Viewer} to invoke {@link Viewer#refresh()} on.
    */
   public static void refresh(final Viewer viewer) {
      if (viewer != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               viewer.refresh();
            }
         });
      }
   }

   /**
    * Invokes {@link AbstractTableViewer#replace(Object, int)} thread save.
    * @param viewer The {@link AbstractTableViewer} to invoke method on.
    * @param element The new element.
    * @param index The index to replace element at.
    */
   public static void replace(final AbstractTableViewer viewer, final Object element, final int index) {
      if (viewer != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               viewer.replace(element, index);
            }
         });
      }
   }

   /**
    * Invokes {@link AbstractTableViewer#add(Object)} thread save.
    * @param viewer The {@link AbstractTableViewer} to invoke method on.
    * @param element The new element to add.
    */
   public static void add(final AbstractTableViewer viewer, final Object element) {
      if (viewer != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               viewer.add(element);
            }
         });
      }
   }

   /**
    * Invokes {@link AbstractTableViewer#add(Object)} thread save.
    * @param viewer The {@link AbstractTableViewer} to invoke method on.
    * @param elements The new elements to add.
    */
   public static void add(final AbstractTableViewer viewer, final Object[] elements) {
      if (viewer != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               viewer.add(elements);
            }
         });
      }
   }

   /**
    * Invokes {@link AbstractTableViewer#remove(Object)} thread save.
    * @param viewer The {@link AbstractTableViewer} to invoke method on.
    * @param element The old element to remove.
    */
   public static void remove(final AbstractTableViewer viewer, final Object element) {
      if (viewer != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               viewer.remove(element);
            }
         });
      }
   }

   /**
    * Invokes {@link AbstractTableViewer#remove(Object)} thread save.
    * @param viewer The {@link AbstractTableViewer} to invoke method on.
    * @param elements The old elements to remove.
    */
   public static void remove(final AbstractTableViewer viewer, final Object[] elements) {
      if (viewer != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               viewer.remove(elements);
            }
         });
      }
   }

   /**
    * Invokes {@link AbstractTableViewer#add(Object)} thread save.
    * @param viewer The {@link AbstractTableViewer} to invoke method on.
    * @param elements The new elements to add.
    */
   public static void addAsync(final AbstractTableViewer viewer, final Object[] elements) {
      if (viewer != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               viewer.add(elements);
            }
         });
      }
   }

   /**
    * Invokes {@link AbstractTableViewer#remove(Object)} thread save.
    * @param viewer The {@link AbstractTableViewer} to invoke method on.
    * @param element The old element to remove.
    */
   public static void removeAsync(final AbstractTableViewer viewer, final Object element) {
      if (viewer != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               viewer.remove(element);
            }
         });
      }
   }

   /**
    * Invokes {@link AbstractTableViewer#remove(Object)} thread save.
    * @param viewer The {@link AbstractTableViewer} to invoke method on.
    * @param elements The old elements to remove.
    */
   public static void removeAsync(final AbstractTableViewer viewer, final Object[] elements) {
      if (viewer != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               viewer.remove(elements);
            }
         });
      }
   }

   /**
    * Invokes {@link CheckboxTableViewer#setChecked(Object, boolean)} thread save.
    * @param viewer The {@link AbstractTableViewer} to invoke method on.
    * @param element The element to modify its checked state.
    * @param state The new checked state to set.
    */
   public static void setChecked(final CheckboxTableViewer viewer, final Object element, final boolean state) {
      if (viewer != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               viewer.setChecked(element, state);
            }
         });
      }
   }

   /**
    * Invokes {@link StructuredViewer#testFindItem(Object)} thread save.
    * @param viewer The {@link StructuredViewer} to invoke method on.
    * @param element The element to test.
    * @return The found {@link Item} or {@code null} if not available.
    */
   public static Object testFindItem(final StructuredViewer viewer, final Object element) {
      IRunnableWithResult<Object> run = new AbstractRunnableWithResult<Object>() {
         @Override
         public void run() {
            setResult(viewer.testFindItem(element));
         }
      };
      viewer.getControl().getDisplay().syncExec(run);
      return run.getResult();
   }
}