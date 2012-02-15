package org.key_project.key4eclipse.util.eclipse.swt;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.internal.ui.viewsupport.FilteredElementTreeSelectionDialog;
import org.eclipse.jdt.internal.ui.wizards.TypedViewerFilter;
import org.eclipse.jdt.internal.ui.wizards.buildpaths.FolderSelectionDialog;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ElementTreeSelectionDialog;
import org.eclipse.ui.model.WorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;
import org.eclipse.ui.views.navigator.ResourceComparator;
import org.key_project.key4eclipse.util.eclipse.swt.viewer.FileSelectionValidator;
import org.key_project.key4eclipse.util.java.StringUtil;

/**
 * Provides utility methods for SWT.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public final class SWTUtil {
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
                    event.gc.drawImage(item.getImage(), event.x, event.y);
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
     * Opens a select folder dialog.
     * @param parent The parent {@link Shell}.
     * @param title The title.
     * @param message The message. 
     * @param allowMultipleSelection Allow multiple selections?
     * @param initialSelection Optional initial selection.
     * @param viewerFilters Optional viewer filters.
     * @return The selected {@link IContainer}s or {@code null} if the dialog was canceled.
     */
    public static IContainer[] openFolderSelection(Shell parent,
                                                   String title,
                                                   String message,
                                                   boolean allowMultipleSelection,
                                                   Object[] initialSelection,
                                                   Collection<? extends ViewerFilter> viewerFilters) {
        ILabelProvider labelProvider = new WorkbenchLabelProvider();
        ITreeContentProvider contentProvider = new WorkbenchContentProvider();
        FolderSelectionDialog dialog = new FolderSelectionDialog(parent, labelProvider, contentProvider);
        dialog.setInput(ResourcesPlugin.getWorkspace().getRoot());
        dialog.setTitle(title);
        dialog.setMessage(message);
        dialog.setAllowMultiple(allowMultipleSelection);
        if (initialSelection != null) {
            dialog.setInitialSelections(initialSelection);
        }
        ViewerFilter projectAndFolderFilter = new TypedViewerFilter(new Class[] {IProject.class, IFolder.class});
        dialog.addFilter(projectAndFolderFilter);
        if (viewerFilters != null) {
            for (ViewerFilter filter : viewerFilters) {
                dialog.addFilter(filter);
            }
        }
        dialog.setComparator(new ResourceComparator(ResourceComparator.NAME));
        if (dialog.open() == FolderSelectionDialog.OK) {
            Object[] result = dialog.getResult();
            List<IContainer> containerResult = new ArrayList<IContainer>(result.length);
            for (Object obj : result) {
                if (obj instanceof IContainer) {
                    containerResult.add((IContainer)obj);
                }
            }
            return containerResult.toArray(new IContainer[containerResult.size()]);
        }
        else {
            return null;
        }
    }
    
    /**
     * Opens a select folder dialog.
     * @param parent The parent {@link Shell}.
     * @param title The title.
     * @param message The message. 
     * @param allowMultipleSelection Allow multiple selections?
     * @param initialSelection Optional initial selection.
     * @param viewerFilters Optional viewer filters.
     * @return The selected {@link IContainer}s or {@code null} if the dialog was canceled.
     */
    public static IFile[] openFileSelection(Shell parent,
                                            String title,
                                            String message,
                                            boolean allowMultipleSelection,
                                            Object[] initialSelection,
                                            Collection<? extends ViewerFilter> viewerFilters) {
        ILabelProvider labelProvider = new WorkbenchLabelProvider();
        ITreeContentProvider contentProvider = new WorkbenchContentProvider();
        ElementTreeSelectionDialog dialog = new FilteredElementTreeSelectionDialog(parent, labelProvider, contentProvider);
        dialog.setInput(ResourcesPlugin.getWorkspace().getRoot());
        dialog.setTitle(title);
        dialog.setMessage(message);
        dialog.setAllowMultiple(allowMultipleSelection);
        if (initialSelection != null) {
            dialog.setInitialSelections(initialSelection);
        }
        if (viewerFilters != null) {
            for (ViewerFilter filter : viewerFilters) {
                dialog.addFilter(filter);
            }
        }
        dialog.setComparator(new ResourceComparator(ResourceComparator.NAME));
        dialog.setValidator(new FileSelectionValidator(false, allowMultipleSelection));
        if (dialog.open() == FolderSelectionDialog.OK) {
            Object[] result = dialog.getResult();
            List<IFile> containerResult = new ArrayList<IFile>(result.length);
            for (Object obj : result) {
                if (obj instanceof IFile) {
                    containerResult.add((IFile)obj);
                }
            }
            return containerResult.toArray(new IFile[containerResult.size()]);
        }
        else {
            return null;
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
                        sb.append("; ");
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
                            sb.append("; ");
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
}
