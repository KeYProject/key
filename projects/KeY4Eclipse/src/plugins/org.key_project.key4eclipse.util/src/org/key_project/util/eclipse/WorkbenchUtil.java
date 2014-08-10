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

package org.key_project.util.eclipse;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jdt.internal.ui.viewsupport.FilteredElementTreeSelectionDialog;
import org.eclipse.jdt.internal.ui.wizards.TypedViewerFilter;
import org.eclipse.jdt.internal.ui.wizards.buildpaths.FolderSelectionDialog;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.ElementTreeSelectionDialog;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.internal.WorkbenchWindow;
import org.eclipse.ui.model.WorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;
import org.eclipse.ui.services.IEvaluationService;
import org.eclipse.ui.views.navigator.ResourceComparator;
import org.eclipse.ui.wizards.newresource.BasicNewFolderResourceWizard;
import org.key_project.util.eclipse.swt.viewer.FileSelectionValidator;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * Provides static methods 
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
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
     * Opens the perspective with the given ID in the active {@link IWorkbenchPage}.
     * @param perspectiveId The ID of the perspective to open.
     * @return The opened {@link IPerspectiveDescriptor} or {@code null} if no {@link IWorkbenchPage} is active.
     */
    public static IPerspectiveDescriptor openPerspective(String perspectiveId) {
       IWorkbenchPage page = getActivePage();
       if (page != null) {
          IPerspectiveDescriptor perspective = PlatformUI.getWorkbench().getPerspectiveRegistry().findPerspectiveWithId(perspectiveId);
          page.setPerspective(perspective);
          return perspective;
       }
       else {
          return null;
       }
    }

    /**
     * Closes the given {@link IPerspectiveDescriptor} in the active {@link IWorkbenchPage}.
     * @param perspectiveToClose The {@link IPerspectiveDescriptor} to close.
     * @param saveParts Whether the page's parts should be saved if closed
     * @param closePage Close the {@link IWorkbenchPage}? 
     */
    public static void closePerspective(IPerspectiveDescriptor perspectiveToClose, boolean saveParts, boolean closePage) {
       if (perspectiveToClose != null) {
          IWorkbenchPage page = getActivePage();
          if (page != null) {
             page.closePerspective(perspectiveToClose, saveParts, closePage);
          }
       }
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
     * Returns the active {@link IWorkbenchPart} if available.
     * @return The active {@link IWorkbenchPart} or {@code null} if no one is available.
     */
    public static IWorkbenchPart getActivePart() {
        IWorkbenchPage page = getActivePage();
        if (page != null) {
            return page.getActivePart();
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

    /**
     * Shows the view identified by the given view id in this page and gives it focus. 
     * If there is a view identified by the given view id (and with no secondary id) already open in this page, 
     * it is given focus.
     * @param viewId The ID of the view to open.
     * @return The opened or reactivated {@link IViewPart} that has now the focus.
     * @throws PartInitException Occurred Exception.
     */
    public static IViewPart openView(String viewId) throws PartInitException {
        IWorkbenchPage page = getActivePage();
        if (page != null) {
            return page.showView(viewId);
        }
        else {
            return null;
        }
    }
    
    /**
     * Checks if the given {@link IWorkbenchPart} is active.
     * @param part The {@link IWorkbenchPart} to check.
     * @return {@code true} is active, {@code false} is not active.
     */
    public static boolean isActive(IWorkbenchPart part) {
        return part != null && part.getSite().getPage().getActivePart() == part;
    }

    /**
     * Activates the given part. The part will be brought to the front and given focus. The part must belong to this page.
     * @param part Activates the given {@link IWorkbenchPart}.
     */
    public static void activate(IWorkbenchPart part) {
        if (part != null) {
            part.getSite().getPage().activate(part);
        }
    }

    /**
     * Closes the given {@link IViewPart}. 
     * @param part The {@link IViewPart} to close.
     */
    public static void closeView(IViewPart view) {
        if (view != null) {
           view.getSite().getPage().hideView(view);
        }
    }

    /**
     * Searches an {@link IViewPart} with the given ID in the active {@link IWorkbenchPage}.
     * @param viewId The view ID to search.
     * @return The found {@link IViewPart} or {@code null} if no one was found.
     */
    public static IViewPart findView(String viewId) {
        IWorkbenchPage page = getActivePage();
        return page != null ? page.findView(viewId) : null;
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
     * Opens a select file dialog.
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
     * Returns the name of the perspective with the given ID.
     * @param perspectiveId The ID of the perspective.
     * @return The name of the perspective or {@code null} if no perspective is available with the given ID.
     */
    public static String getPerspectiveName(String perspectiveId) {
        IPerspectiveDescriptor perspective = PlatformUI.getWorkbench().getPerspectiveRegistry().findPerspectiveWithId(perspectiveId);
        return perspective != null ? perspective.getLabel() : null;
    }
    
    /**
     * Checks if a perspective with the given ID is currently opened in the given {@link IWorkbenchPage}.
     * @param perspectiveId The perspective ID to check.
     * @param page The {@link IWorkbenchPage} to check opened perspective in.
     * @return {@code true} perspective is currently opened in the given {@link IWorkbenchPage}, {@code false} perspective is not opened in the given {@link IWorkbenchPage}.
     */
    public static boolean isPerspectiveOpen(String perspectiveId, IWorkbenchPage page) {
       if (page != null) {
          IPerspectiveDescriptor pd = page.getPerspective();
          if (pd != null) {
             return ObjectUtil.equals(perspectiveId, page.getPerspective().getId());
          }
          else {
             return false;
          }
       }
       else {
          return false;
       }
    }

   /**
    * Re-Evaluates all specified {@code PropertyTester}.  
    * @param properties The properties to re-evaluate.
    */
   public static void updatePropertyTesters(final String... properties) {
      if (properties != null) {
         Display.getDefault().syncExec(new Runnable() {
            @Override
            public void run() {
               IWorkbenchWindow window = getActiveWorkbenchWindow();
               if (window != null) {
                  IEvaluationService service = (IEvaluationService)window.getService(IEvaluationService.class);
                  if (service != null) {
                     for (String property : properties) {
                        service.requestEvaluation(property);
                     }
                  }
               }
            }
         });
      }
   }

   /**
    * Updates the toolbars (action bars) of all {@link IWorkbenchWindow}s.
    */
   public static void updateToolBars() {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            IWorkbenchWindow[] windows = PlatformUI.getWorkbench().getWorkbenchWindows();
            for (IWorkbenchWindow window : windows) {
               if (window instanceof WorkbenchWindow) {
                  ((WorkbenchWindow)window).updateActionBars();
                  ((WorkbenchWindow)window).updateActionSets();
               }
            }
         }
      });
   }

   /**
    * Searches the {@link IWorkbenchWindow} for the given {@link Shell}.
    * @param shell The {@link Shell} for which the {@link IWorkbenchWindow} is requested.
    * @return The found {@link IWorkbenchWindow} of the given {@link Shell} or {@code null} if not available.
    */
   public static IWorkbenchWindow findWorkbenchWindow(final Shell shell) {
      IWorkbenchWindow[] windows = PlatformUI.getWorkbench().getWorkbenchWindows();
      return ArrayUtil.search(windows, new IFilter<IWorkbenchWindow>() {
         @Override
         public boolean select(IWorkbenchWindow element) {
            return element.getShell() == shell;
         }
      });
   }
}