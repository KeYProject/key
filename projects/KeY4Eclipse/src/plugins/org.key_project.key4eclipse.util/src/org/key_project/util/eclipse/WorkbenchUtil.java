package org.key_project.util.eclipse;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.wizards.newresource.BasicNewFolderResourceWizard;

/**
 * Provides static methods 
 * @author Martin Hentschel
 */
public final class WorkbenchUtil {
    /**
     * The ID of the default text editor.
     */
    public static final String DEFAULT_TEXT_EDITOR_ID = "org.eclipse.ui.DefaultTextEditor";
    
    /**
     * Forbid instances.
     */
    private WorkbenchUtil() {
    }
    
    /**
     * Returns the active {@link IWorkbenchWindow} if available.
     * @return The active {@link IWorkbenchWindow} or {@code null} if no one is available.
     */
    public static IWorkbenchWindow getActiveWorkbenchWindow() {
        IWorkbench workbench = PlatformUI.getWorkbench();
        if (workbench != null) {
            return workbench.getActiveWorkbenchWindow();
        }
        else {
            return null;
        }
    }
    
    /**
     * Returns the active {@link IWorkbenchPage} if available.
     * @return The active {@link IWorkbenchPage} or {@code null} if no one is available.
     */
    public static IWorkbenchPage getActivePage() {
        IWorkbenchWindow window = getActiveWorkbenchWindow();
        if (window != null) {
            return window.getActivePage();
        }
        else {
            return null;
        }
    }
    
    /**
     * Returns the active {@link IEditorPart} if available.
     * @return The active {@link IEditorPart} or {@code null} if no one is available.
     */
    public static IEditorPart getActiveEditor() {
        IWorkbenchPage page = getActivePage();
        if (page != null) {
            return page.getActiveEditor();
        }
        else {
            return null;
        }
    }
    
    /**
     * Returns the active {@link Shell} if available.
     * @return The active {@link Shell} or {@code null} if no one is available.
     */
    public static Shell getActiveShell() {
        IWorkbenchWindow window = getActiveWorkbenchWindow();
        if (window != null) {
            return window.getShell();
        }
        else {
            return null;
        }
    }
    
    /**
     * Selects and reveals the given {@link IResource}.
     * @param resource The {@link IResource} to show.
     */
    public static void selectAndReveal(IResource resource) {
        IWorkbench workbench = PlatformUI.getWorkbench();
        if (workbench != null) {
            IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
            if (window != null) {
                BasicNewFolderResourceWizard.selectAndReveal(resource, window);
            }
        }
    }
    
    /**
     * Opens an eclipse editor for the given {@link IFile}. 
     * @param file The {@link IFile} to open.
     * @return The opened eclipse editor.
     * @throws PartInitException Occurred Exception.
     */
    public static IEditorPart openEditor(IFile file) throws PartInitException {
        if (file != null) {
            IWorkbench workbench = PlatformUI.getWorkbench();
            if (workbench != null) {
                IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
                if (window != null) {
                    IWorkbenchPage page = window.getActivePage();
                    if (page != null) {
                        return IDE.openEditor(page, file);
                    }
                    else {
                        throw new PartInitException("Active workbench page is not available");
                    }
                }
                else {
                    throw new PartInitException("Active workbench window is not available");
                }
            }
            else {
                throw new PartInitException("Workbench is not available");
            }
        }
        else {
            throw new PartInitException("No file to open defined.");
        }
    }

    /**
     * Closes the given eclipse editor.
     * @param editor The editor to close.
     * @param save Save changes?
     * @return {@code true} if the editor was successfully closed, and {@code false} if the editor is still open.
     */
    public static boolean closeEditor(IEditorPart editor, boolean save) {
        if (editor != null) {
            boolean closed = false;
            IEditorSite site = editor.getEditorSite();
            if (site != null) {
                IWorkbenchPage page = site.getPage();
                if (page != null) {
                    closed = page.closeEditor(editor, save);
                }
            }
            return closed;
        }
        else {
            return true;
        }
    }
}
