package org.key_project.sed.key.evaluation.model.definition;

import java.io.File;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.List;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.swt.SWTError;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.sed.key.evaluation.model.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.ObjectUtil;

public abstract class AbstractEvaluation {
   private final String name;
   
   private final List<Tool> tools;
   
   private final List<AbstractForm> forms;
   
   private final String bundlePathsNeededToBeLocal;
   
   private final File stateEvaluationFolder;
   
   public AbstractEvaluation(String name, String bundlePathsNeededToBeLocal) {
      this.name = name;
      this.bundlePathsNeededToBeLocal = bundlePathsNeededToBeLocal;
      this.stateEvaluationFolder = createLocalEvaluationFolder(bundlePathsNeededToBeLocal);
      this.tools = computeTools();
      this.forms = (List<AbstractForm>)computeForms();
      for (AbstractForm form : forms) {
         form.setEvaluation(this);
      }
   }

   public static AbstractEvaluation[] getEvaluations() {
      return new AbstractEvaluation[] {UnderstandingProofAttemptsEvaluation.INSTANCE, 
                                       ReviewingCodeEvaluation.INSTANCE,
                                       TestEvaluation.INSTANCE,
                                       BrowserExampleEvaluation.INSTANCE};
   }
   
   public static AbstractEvaluation getEvaluationForName(final String name) {
      return ArrayUtil.search(getEvaluations(), new IFilter<AbstractEvaluation>() {
         @Override
         public boolean select(AbstractEvaluation element) {
            return ObjectUtil.equals(element.getName(), name);
         }
      });
   }
   
   /**
    * Creates a local folder in the state location of this plug-in
    * filled with the content specified by the given path.
    * @param bundlePathsNeededToBeLocal The path to make its content local.
    * @return The created folder or {@code null} if nothing needs to be done.
    */
   protected File createLocalEvaluationFolder(String bundlePathsNeededToBeLocal) {
      try {
         if (bundlePathsNeededToBeLocal != null && !isBundlePathLocalDirectory(bundlePathsNeededToBeLocal)) {
            String statePath = Activator.getDefault().getStateLocation().toString();
            File stateEvaluationFolder = new File(statePath, name);
            IOUtil.delete(stateEvaluationFolder);
            stateEvaluationFolder.mkdirs();
            BundleUtil.extractFromBundleToFilesystem(Activator.PLUGIN_ID, bundlePathsNeededToBeLocal, stateEvaluationFolder);
            return stateEvaluationFolder;
         }
         else {
            return null;
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError("Can't make path '" + bundlePathsNeededToBeLocal + "' local.", e);
         return null;
      }
   }
   
   /**
    * Checks if the given path is local.
    * @param bundlePath The bundle path to check.
    * @return {@code true} bundle path is a local directory, {@code false} otherwise.
    */
   protected boolean isBundlePathLocalDirectory(String bundlePath) {
      try {
         URL url = Activator.getDefault().getBundle().getEntry(bundlePath);
         URL fileUrl = FileLocator.resolve(url);
         File file = IOUtil.toFile(fileUrl);
         return file != null && file.isDirectory();
      }
      catch (Exception e) {
         return false;
      }
   }

   /**
    * Converts the given bundle path into a local {@link URL}.
    * @param bundlePath The bundle path.
    * @return The local {@link URL} or {@code null} if something went wrong.
    */
   protected URL toLocalURL(String bundlePath) {
      try {
         if (bundlePath != null) {
            if (stateEvaluationFolder != null && bundlePath.startsWith(bundlePathsNeededToBeLocal)) {
               String subPath = bundlePath.substring(bundlePathsNeededToBeLocal.length());
               return new File (stateEvaluationFolder, subPath).toURI().toURL();
            }
            else {
               return Activator.getDefault().getBundle().getEntry(bundlePath);
            }
         }
         else {
            return null;
         }
      }
      catch (MalformedURLException e) {
         LogUtil.getLogger().logError("Can't make path '" + bundlePath + "' local.", e);
         return null;
      }
   }

   protected abstract List<Tool> computeTools();

   protected abstract List<AbstractForm> computeForms();

   public String getName() {
      return name;
   }
   
   public Tool[] getTools() {
      return tools.toArray(new Tool[tools.size()]);
   }
   
   public AbstractForm[] getForms() {
      return forms.toArray(new AbstractForm[forms.size()]);
   }

   public int countForms() {
      return forms.size();
   }

   public AbstractForm getForm(final String formName) {
      return CollectionUtil.search(forms, new IFilter<AbstractForm>() {
         @Override
         public boolean select(AbstractForm element) {
            return ObjectUtil.equals(formName, element.getName());
         }
      });
   }

   public Tool getTool(final String toolName) {
      return CollectionUtil.search(tools, new IFilter<Tool>() {
         @Override
         public boolean select(Tool element) {
            return ObjectUtil.equals(toolName, element.getName());
         }
      });
   }
   
   /**
    * Checks if the user interface is available.
    * @return {@code true} user interface available, {@code false} user interface not available.
    */
   protected static boolean isUIAvailable() {
      try {
         return Activator.getDefault() != null && Display.getDefault() != null && !Display.getDefault().isDisposed();
      }
      catch (SWTError e) { // Thrown if a graphical user interface is not available.
         return false;
      }
   }
}
