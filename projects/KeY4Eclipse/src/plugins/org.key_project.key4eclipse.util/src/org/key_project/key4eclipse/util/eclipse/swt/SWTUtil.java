package org.key_project.key4eclipse.util.eclipse.swt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jdt.internal.ui.viewsupport.FilteredElementTreeSelectionDialog;
import org.eclipse.jdt.internal.ui.wizards.TypedViewerFilter;
import org.eclipse.jdt.internal.ui.wizards.buildpaths.FolderSelectionDialog;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.widgets.Shell;
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
}
