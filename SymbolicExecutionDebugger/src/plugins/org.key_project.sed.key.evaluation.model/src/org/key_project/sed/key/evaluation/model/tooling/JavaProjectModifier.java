package org.key_project.sed.key.evaluation.model.tooling;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditorPreferenceConstants;
import org.key_project.sed.key.evaluation.model.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.jdt.JDTUtil;

public class JavaProjectModifier extends AbstractWorkbenchModifier {
   public static final String BINARY_FOLDER_NAME = "bin";
   public static final String SOURCE_FOLDER_NAME = "src";
   
   private final FileDefinition[] files;
   
   private IJavaProject javaProject;
   
   private boolean originalShowLineNumbers;
   
   public JavaProjectModifier(FileDefinition... files) {
      this.files = files;
   }

   @Override
   public synchronized String modifyWorkbench() throws Exception {
      if (javaProject == null) {
         setShowLineNumbers();
         String projectName = getPageInput().getFormInput().getEvaluationInput().getEvaluation().getName();
         IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
         int counter = 1;
         while (project.exists()) {
            project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName + "_" + counter);
            counter++;
         }
         javaProject = JDTUtil.createJavaProject(project.getName(), BINARY_FOLDER_NAME, new String[] {SOURCE_FOLDER_NAME});
         for (FileDefinition definition : getFilesToExtract()) {
            extractFileDefinition(definition);
         }
         finalizeJavaProject(javaProject);
         return getCompletionMessage();
      }
      else {
         // Workspace was already modified, nothing to do.
         return null;
      }
   }
   
   protected FileDefinition[] getFilesToExtract() {
      return files;
   }
   
   protected void finalizeJavaProject(IJavaProject javaProject) throws Exception {
   }

   protected void setShowLineNumbers() {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            originalShowLineNumbers = EditorsUI.getPreferenceStore().getBoolean(AbstractDecoratedTextEditorPreferenceConstants.EDITOR_LINE_NUMBER_RULER);
            EditorsUI.getPreferenceStore().setValue(AbstractDecoratedTextEditorPreferenceConstants.EDITOR_LINE_NUMBER_RULER, true);
         }
      });
   }
   
   protected IFile extractFileDefinition(FileDefinition definition) throws Exception {
      final IFile projectFile = javaProject.getProject().getFile(new Path(definition.getPathInProject()));
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, definition.getPathInBundle(), projectFile);
      if (definition.isOpen()) {
         IRunnableWithException run = new AbstractRunnableWithException() {
            @Override
            public void run() {
               try {
                  WorkbenchUtil.openEditor(projectFile);
               }
               catch (Exception e) {
                  setException(e);
               }
            }
         };
         getShell().getDisplay().syncExec(run);
         if (run.getException() != null) {
            throw run.getException();
         }
      }
      fileCreated(definition, projectFile);
      return projectFile;
   }

   protected void fileCreated(FileDefinition definition, IFile projectFile) throws Exception {
   }

   @Override
   public synchronized void cleanWorkbench() throws Exception {
      if (javaProject != null) {
         javaProject.getProject().delete(true, null);
         Display.getDefault().syncExec(new Runnable() {
            @Override
            public void run() {
               EditorsUI.getPreferenceStore().setValue(AbstractDecoratedTextEditorPreferenceConstants.EDITOR_LINE_NUMBER_RULER, originalShowLineNumbers);
            }
         });
         doAdditinalCleanup();
         javaProject = null;
      }
      else {
         // Workspace was already cleaned, nothing to do.
      }
   }
   
   protected void doAdditinalCleanup() throws Exception {
   }

   public IJavaProject getJavaProject() {
      return javaProject;
   }
   
   protected String getCompletionMessage() {
      return null;
   }

   public static class FileDefinition {
      private final String pathInBundle;
      
      private final String pathInProject;
      
      private final boolean open;

      public FileDefinition(String pathInBundle, String pathInProject, boolean open) {
         this.pathInBundle = pathInBundle;
         this.pathInProject = pathInProject;
         this.open = open;
      }

      public String getPathInBundle() {
         return pathInBundle;
      }

      public String getPathInProject() {
         return pathInProject;
      }

      public boolean isOpen() {
         return open;
      }      
   }
}
