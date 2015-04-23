package org.key_project.removegenerics.ui.wizard;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.removegenerics.ui.util.LogUtil;
import org.key_project.removegenerics.ui.wizard.page.RemoveGenericsPreviewWizardPage;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.util.removegenerics.PreviewGenericRemover;
import de.uka.ilkd.key.util.removegenerics.monitor.GenericRemoverMonitor;

/**
 * {@link Wizard} to remove generics.
 * @author Martin Hentschel
 *
 */
public class RemoveGenericsWizard extends Wizard {
   /**
    * The {@link IJavaProject} to modify.
    */
   private final IJavaProject javaProject;
   
   /**
    * The {@link IResource} containing the source code treated by KeY.
    */
   private final IResource source;

   /**
    * The shown {@link RemoveGenericsPreviewWizardPage}.
    */
   private final RemoveGenericsPreviewWizardPage previewPage;
   
   /**
    * Constructor.
    * @param javaProject The {@link IJavaProject} to modify.
    * @throws CoreException Occurred Exception.
    */
   public RemoveGenericsWizard(IJavaProject javaProject) throws CoreException {
      this.javaProject = javaProject;
      this.source = KeYResourceProperties.getSourceClassPathResource(javaProject.getProject());
      this.previewPage = new RemoveGenericsPreviewWizardPage("previewPage", source);
      setNeedsProgressMonitor(true);
      setHelpAvailable(false);
      setWindowTitle("Remove Generics");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      addPage(previewPage);
      getShell().getDisplay().asyncExec(new Runnable() {
         @Override
         public void run() {
            handleWizardDialogOpened();
         }
      });
   }

   /**
    * When the {@link WizardDialog} is opened.
    */
   protected void handleWizardDialogOpened() {
      try {
         getContainer().run(true, true, new IRunnableWithProgress() {
            @Override
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
               try {
                  removeGeneris(monitor);
               }
               catch (OperationCanceledException e) {
                  throw new InterruptedException("Remove Generics Cancelled");
               }
               catch (Exception e) {
                  throw new InvocationTargetException(e);
               }
            }
         });
      }
      catch (InterruptedException e) {
         ((WizardDialog) getContainer()).close();
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         ((WizardDialog) getContainer()).close();
      }
   }

   /**
    * Removes the generics (preview only)
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws Exception Occurred Exception.
    */
   protected void removeGeneris(final IProgressMonitor monitor) throws Exception {
      // Create remover
      SWTUtil.checkCanceled(monitor);
      final WrapperGenericRemoverMonitor removerMonitor = new WrapperGenericRemoverMonitor(monitor);
      final PreviewGenericRemover remover = new PreviewGenericRemover(removerMonitor);
      final Map<File, IFile> fileToResourceMap = new HashMap<File, IFile>();
      // List libraries
      SWTUtil.checkCanceled(monitor);
      Set<IProject> alreadyHandledProjects = new HashSet<IProject>();
      IClasspathEntry[] entries = javaProject.getRawClasspath();
      monitor.beginTask("Listing libraries", entries.length);
      for (IClasspathEntry entry : entries) {
         SWTUtil.checkCanceled(monitor);
         List<File> locations = JDTUtil.getLocationFor(javaProject, entry, IPackageFragmentRoot.K_BINARY, alreadyHandledProjects);
         for (File location : locations) {
            remover.addSearchPath(location.getAbsolutePath());
         }
         monitor.worked(1);
      }
      monitor.done();
      // List source files
      SWTUtil.checkCanceled(monitor);
      monitor.beginTask("Listing source files", IProgressMonitor.UNKNOWN);
      source.accept(new IResourceVisitor() {
         @Override
         public boolean visit(IResource resource) throws CoreException {
            SWTUtil.checkCanceled(monitor);
            if (JDTUtil.isJavaFile(resource)) {
               File localFile = ResourceUtil.getLocation(resource);
               remover.addSourceFile(localFile.getAbsolutePath());
               fileToResourceMap.put(localFile, (IFile) resource);
            }
            monitor.worked(1);
            return true;
         }
      });
      // Remove generics and store result in a temporary directory.
      remover.removeGenerics();
      // Map new content back to resources
      monitor.beginTask("Assigning new content to resources", remover.getResultMap().size());
      Map<IFile, String> contentMap = new HashMap<IFile, String>();
      for (Entry<File, String> entry: remover.getResultMap().entrySet()) {
         SWTUtil.checkCanceled(monitor);
         IFile resource = fileToResourceMap.get(entry.getKey());
         assert resource != null;
         contentMap.put(resource, entry.getValue());
         monitor.worked(1);
      }
      previewPage.setContentMap(contentMap);
      monitor.done();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      final Map<IFile, String> contentMap = previewPage.getContentMap();
      try {
         getContainer().run(true, true, new IRunnableWithProgress() {
            @Override
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
               try {
                  IWorkspaceRunnable action = new IWorkspaceRunnable() {
                     @Override
                     public void run(IProgressMonitor monitor) throws CoreException {
                        monitor.beginTask("Updating files", contentMap.size());
                        for (Entry<IFile, String> entry : contentMap.entrySet()) {
                           SWTUtil.checkCanceled(monitor);
                           if (entry.getKey().exists()) {
                              entry.getKey().setContents(new ByteArrayInputStream(entry.getValue().getBytes()), true, true, null);
                           }
                           else {
                              entry.getKey().create(new ByteArrayInputStream(entry.getValue().getBytes()), true, null);
                           }
                           monitor.worked(1);
                        }
                        monitor.done();
                     }                  
                  };
                  ResourcesPlugin.getWorkspace().run(action, monitor);
               }
               catch (OperationCanceledException e) {
                  throw new InterruptedException();
               }
               catch (CoreException e) {
                  throw new InvocationTargetException(e);
               }
            }
         });
         return true;
      }
      catch (InvocationTargetException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         return false;
      }
      catch (InterruptedException e) {
         return false;
      }
   }
   
   /**
    * Opens the {@link RemoveGenericsWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param target The {@link IJavaProject} to remove generics in.
    * @return The dialog result.
    * @throws CoreException Occurred Exception.
    */
   public static int openWizard(Shell parentShell, IJavaProject javaProject) throws CoreException {
      WizardDialog dialog = new WizardDialog(parentShell, new RemoveGenericsWizard(javaProject));
      dialog.setHelpAvailable(false);
      return dialog.open();
   }
   
   /**
    * A {@link GenericRemoverMonitor} which updates an {@link IProgressMonitor}.
    * @author Martin Hentschel
    */
   private static class WrapperGenericRemoverMonitor implements GenericRemoverMonitor {
      /**
       * The {@link IProgressMonitor} to use.
       */
      private final IProgressMonitor monitor;

      /**
       * Constructor.
       * @param monitor The {@link IProgressMonitor} to use.
       */
      public WrapperGenericRemoverMonitor(IProgressMonitor monitor) {
         this.monitor = monitor;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void taskStarted(String message) {
         monitor.beginTask(message, IProgressMonitor.UNKNOWN);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void warningOccurred(String message) {
         LogUtil.getLogger().logWarning(message);
      }
   }
}
