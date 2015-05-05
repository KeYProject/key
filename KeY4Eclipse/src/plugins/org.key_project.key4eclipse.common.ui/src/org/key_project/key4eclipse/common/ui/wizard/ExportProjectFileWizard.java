package org.key_project.key4eclipse.common.ui.wizard;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.IExportWizard;
import org.eclipse.ui.IWorkbench;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.common.ui.wizard.page.ExportProjectFileWizardPage;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.util.MiscTools;

/**
 * The {@link IExportWizard} to export KeY's project settings into a {@code project.key} file.
 * @author Martin Hentschel
 */
public class ExportProjectFileWizard extends Wizard implements IExportWizard {
   /**
    * The shown {@link ExportProjectFileWizardPage}.
    */
   private ExportProjectFileWizardPage exportPage;
   
   /**
    * The selected {@link IProject} if available or {@code null} otherwise.
    */
   private IProject selectedProject;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench, IStructuredSelection selection) {
      setWindowTitle("Export Project.key File");
      setNeedsProgressMonitor(true);
      setHelpAvailable(false);
      // Check if a project is selected
      Object[] elements = SWTUtil.toArray(selection);
      int i = 0;
      while (selectedProject == null && i < elements.length) {
         if (elements[i] instanceof IAdaptable) {
            elements[i] = ((IAdaptable) elements[i]).getAdapter(IResource.class);
         }
         if (elements[i] instanceof IResource) {
            selectedProject = ((IResource) elements[i]).getProject();
         }
         i++;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      exportPage = new ExportProjectFileWizardPage("exportPage", selectedProject);
      addPage(exportPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         // Get settings
         IProject project = exportPage.getProject();
         boolean isWorkspace = exportPage.isWorkspace();
         String path = exportPage.getPath();
         // Create file
         if (isWorkspace) {
            IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(path));
            boolean goOn = true;
            if (file.exists()) {
               goOn = askToReplaceFile(path);
            }
            if (goOn) {
               String content = createContent(project, ResourceUtil.getLocation(file));
               ResourceUtil.ensureExists(file.getParent());
               ResourceUtil.createFile(file, new ByteArrayInputStream(content.getBytes()), null);
            }
         }
         else {
            File file = new File(path);
            boolean goOn = true;
            if (file.exists()) {
               goOn = askToReplaceFile(path);
            }
            if (goOn) {
               String content = createContent(project, file);
               file.getParentFile().mkdirs();
               IOUtil.writeTo(new FileOutputStream(file), content);
               IResource[] resources = ResourceUtil.findResourceForLocation(file);
               for (IResource resource : resources) {
                  resource.refreshLocal(IResource.DEPTH_ZERO, null);
               }
            }
         }
         return true;
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         return false;
      }
   }

   /**
    * Asks the user to replace an existing file.
    * @param path The path to the file.
    * @return {@code true} replace it, {@code false} abort export.
    */
   protected boolean askToReplaceFile(String path) {
      return MessageDialog.openQuestion(getShell(), "Overwrite existing file?", "The file '" + path + "' already exists. Overwrite it?");
   }

   /**
    * Creates the new file content.
    * @param project The {@link IProject} to export.
    * @param targetFile The target {@link File}.
    * @return The created content.
    * @throws CoreException Occurred Exception.
    */
   protected String createContent(IProject project, File targetFile) throws CoreException {
      // Get settings
      File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
      List<File> classPath = KeYResourceProperties.getKeYClassPathEntries(project);
      File source = KeYResourceProperties.getSourceClassPathLocation(project);
      List<File> includes = KeYResourceProperties.getKeYIncludes(project);
      // Create content
      boolean afterFirstLine = false;
      StringBuffer sb = new StringBuffer();
      if (bootClassPath != null) {
         if (afterFirstLine) {
            sb.append(StringUtil.NEW_LINE);
         }
         sb.append("\\bootclasspath \"");
         sb.append(makeRelative(bootClassPath, targetFile));
         sb.append("\";" + StringUtil.NEW_LINE);
         afterFirstLine = true;
      }
      if (!CollectionUtil.isEmpty(classPath)) {
         if (afterFirstLine) {
            sb.append(StringUtil.NEW_LINE);
         }
         sb.append("\\classpath ");
         boolean afterFirst = false;
         for (File file : classPath) {
            if (afterFirst) {
               sb.append(", \"");
            }
            else {
               sb.append("\"");
               afterFirst = true;
            }
            sb.append(makeRelative(file, targetFile));
            sb.append("\"");
         }
         sb.append(";" + StringUtil.NEW_LINE);
         afterFirstLine = true;
      }
      if (source != null) {
         if (afterFirstLine) {
            sb.append(StringUtil.NEW_LINE);
         }
         sb.append("\\javaSource \"");
         sb.append(makeRelative(source, targetFile));
         sb.append("\";" + StringUtil.NEW_LINE);
         afterFirstLine = true;
      }
      if (!CollectionUtil.isEmpty(includes)) {
         if (afterFirstLine) {
            sb.append(StringUtil.NEW_LINE);
         }
         sb.append("\\include ");
         boolean afterFirst = false;
         for (File file : includes) {
            if (afterFirst) {
               sb.append(", \"");
            }
            else {
               sb.append("\"");
               afterFirst = true;
            }
            sb.append(makeRelative(file, targetFile));
            sb.append("\"");
         }
         sb.append(";" + StringUtil.NEW_LINE);
         afterFirstLine = true;
      }
      if (afterFirstLine) {
         sb.append(StringUtil.NEW_LINE);
      }
      sb.append("\\chooseContract");
      return sb.toString();
   }
   
   /**
    * Makes the path relative.
    * @param original The original {@link File}.
    * @param relativeToFile The {@link File} to make it relative to.
    * @return The relative path or the absolute one if a relative path is not possible.
    */
   protected String makeRelative(File original, File relativeToFile) {
      try {
         return MiscTools.makeFilenameRelative(original.getAbsolutePath(), relativeToFile.getParentFile().getAbsolutePath());
      }
      catch (Exception e) {
         // Can not compute relative path, return absolute path instead.
         return original.getAbsolutePath();
      }
   }
}
