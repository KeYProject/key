package org.key_project.sed.key.evaluation.model.tooling;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.key.evaluation.model.Activator;
import org.key_project.sed.key.evaluation.model.definition.ReviewingCodeEvaluation;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.util.LogUtil;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.JobUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;

public class ReviewingCodeJavaProjectModifier extends AbstractSEDJavaProjectModifier {
   private final String typeName;
   
   private final ProofFileFileDefinition[] proofFileDefinitions;
   
   private final FileDefinition bootClassPathDefinition;
   
   private final FileDefinition[] noToolFiles;
   
   private IPerspectiveDescriptor originalPerspective;
   
   private final boolean showCompletionMessage;
   
   private final List<ILaunchConfiguration> launchConfigurations = new LinkedList<ILaunchConfiguration>();
   
   private String currentTab;
   
   public ReviewingCodeJavaProjectModifier(String typeName,
                                           boolean showCompletionMessage,
                                           FileDefinition bootClassPathDefinition,
                                           ProofFileFileDefinition[] proofFileDefinitions, 
                                           FileDefinition[] noToolFiles,
                                           FileDefinition... files) {
      super(files);
      this.typeName = typeName;
      this.bootClassPathDefinition = bootClassPathDefinition;
      this.showCompletionMessage = showCompletionMessage;
      this.proofFileDefinitions = proofFileDefinitions;
      this.noToolFiles = noToolFiles;
   }

   @Override
   protected FileDefinition[] getFilesToExtract() {
      if (ReviewingCodeEvaluation.NO_TOOL_NAME.equals(getTool().getName())) {
         if (!ArrayUtil.isEmpty(noToolFiles)) {
            return noToolFiles;
         }
         else {
            return super.getFilesToExtract();
         }
      }
      else {
         return super.getFilesToExtract();
      }
   }

   @Override
   protected String getCompletionMessage() {
      if (showCompletionMessage) {
         if (ReviewingCodeEvaluation.NO_TOOL_NAME.equals(getTool().getName())) {
            return "The source code of '" + typeName + "' is shown in Eclipse.\n" +
                   "Please answer the questions shown in the evaluation wizard.\n" +
                   "Do NOT symbolically debug the source code using SED!";
         }
         else if (ReviewingCodeEvaluation.SED_TOOL_NAME.equals(getTool().getName())) {
            return "The symbolic execution tree of the source code of '" + typeName + "' is shown in Eclipse.\n" +
                   "Please answer the questions shown in the evaluation wizard.\n" +
                   "Do NOT write additional code to be able to execute or debug the source code (concrete execution)!";
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }
   
   @Override
   protected void finalizeJavaProject(IJavaProject javaProject) throws Exception {
      if (getTool() != null) {
         originalPerspective = getWorkbenchPage().getPerspective();
         if (ReviewingCodeEvaluation.NO_TOOL_NAME.equals(getTool().getName())) {
            getWorkbenchPage().setPerspective(WorkbenchUtil.getPerspectiveDescriptor("org.eclipse.jdt.ui.JavaPerspective"));
         }
         else if (ReviewingCodeEvaluation.SED_TOOL_NAME.equals(getTool().getName())) {
            // Open Symbolic Debug perspective
            getWorkbenchPage().setPerspective(WorkbenchUtil.getPerspectiveDescriptor(SymbolicDebugPerspectiveFactory.PERSPECTIVE_ID));
            // Create boot class path folder
            if (bootClassPathDefinition != null) {
               final IFolder projectFolder = javaProject.getProject().getFolder(new Path(bootClassPathDefinition.getPathInProject()));
               BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, bootClassPathDefinition.getPathInBundle(), projectFolder);
               KeYResourceProperties.setBootClassPath(javaProject.getProject(), UseBootClassPathKind.WORKSPACE, projectFolder.getFullPath().toString());
            }
            // Launch proof in SED
            for (ProofFileFileDefinition definition : proofFileDefinitions) {
               IFile projectFile = extractFileDefinition(definition);
               ILaunchConfiguration conf = launchSED(definition.getTypeName(), definition.getMethodName(), definition.getMethodParameters(), projectFile);
               launchConfigurations.add(conf);
            }
         }
      }
      // Wait for jobs
      Thread.sleep(1000); // Give the UI the chance to start Jobs
      JobUtil.waitForJobs(100);
      // Ensure that correct tab is selected.
      selectProofOfTab();
   }

   @Override
   protected Boolean areVariablesAreComputedFromUpdates() {
      return Boolean.TRUE;
   }

   @Override
   protected void doAdditinalCleanup() throws Exception {
      super.doAdditinalCleanup();
      for (ILaunchConfiguration launchConfiguration : launchConfigurations) {
         terminate(launchConfiguration);
      }
      if (originalPerspective != null) {
         Display.getDefault().syncExec(new Runnable() {
            @Override
            public void run() {
               getWorkbenchPage().setPerspective(originalPerspective);
            }
         });
      }
   }
   
   public static class ProofFileFileDefinition extends FileDefinition {
      private final String typeName;
      private final String methodName;
      private final String[] methodParameters; 

      public ProofFileFileDefinition(String pathInBundle, 
                                     String pathInProject, 
                                     boolean open, 
                                     String typeName, 
                                     String methodName, 
                                     String[] methodParameters) {
         super(pathInBundle, pathInProject, open);
         this.typeName = typeName;
         this.methodName = methodName;
         this.methodParameters = methodParameters;
      }

      public String getTypeName() {
         return typeName;
      }

      public String getMethodName() {
         return methodName;
      }

      public String[] getMethodParameters() {
         return methodParameters;
      }
   }

   @Override
   public void selectedTabChanged(QuestionInput questionInput) {
      currentTab = questionInput.getValue();
      selectProofOfTab();
   }
   
   @SuppressWarnings({ "rawtypes", "unchecked" })
   protected void selectProofOfTab() {
      try {
         // Show source code
         if (getJavaProject() != null) {
            final IType type;
            final IMethod method;
            if ("set(int, Object)".equals(currentTab)) {
               type = getJavaProject().findType("ObservableArray");
               method = type.getMethod("set", new String[] {"I", "QObject;"});
            }
            else if ("ObservableArray(Object[])".equals(currentTab)) {
               type = getJavaProject().findType("ObservableArray");
               method = type.getMethod("ObservableArray", new String[] {"[QObject;"});
            }
            else if ("setArrayListeners(ArrayListener[])".equals(currentTab)) {
               type = getJavaProject().findType("ObservableArray");
               method = type.getMethod("setArrayListeners", new String[] {"[QArrayListener;"});
            }
            else if ("Stack(int)".equals(currentTab)) {
               type = getJavaProject().findType("Stack");
               method = type.getMethod("Stack", new String[] {"I"});
            }
            else if ("Stack(Stack)".equals(currentTab)) {
               type = getJavaProject().findType("Stack");
               method = type.getMethod("Stack", new String[] {"QStack;"});
            }
            else if ("push(Object)".equals(currentTab)) {
               type = getJavaProject().findType("Stack");
               method = type.getMethod("push", new String[] {"QObject;"});
            }
            else if ("pop()".equals(currentTab)) {
               type = getJavaProject().findType("Stack");
               method = type.getMethod("pop", new String[0]);
            }
            else {
               type = null;
               method = null;
            }
            IRunnableWithException run = new AbstractRunnableWithException() {
               @Override
               public void run() {
                  try {
                     if (method != null) {
                        JavaUI.openInEditor(method, true, true);
                     }
                     else if (type != null) {
                        JavaUI.openInEditor(type, true, true);
                     }
                  }
                  catch (Exception e) {
                     setException(e);
                  }
               }
            };
            Display.getDefault().syncExec(run);
            if (run.getException() != null) {
               throw run.getException();
            }
         }
         // Select launch
         if (currentTab != null && !launchConfigurations.isEmpty()) {
            final List toSelect = new LinkedList();
            ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
            for (ILaunch launch : launchManager.getLaunches()) {
               final String targetName = launch.getDebugTarget().getName();
               if (!launch.isTerminated() && launchConfigurations.contains(launch.getLaunchConfiguration())) {
                  boolean found = false;
                  if ("set(int, Object)".equals(currentTab) &&
                      "set(int, java.lang.Object)".equals(targetName)) {
                     found = true;
                  }
                  else if ("ObservableArray(Object[])".equals(currentTab) &&
                           "ObservableArray(java.lang.Object[])".equals(targetName)) {
                     found = true;
                  }
                  else if ("setArrayListeners(ArrayListener[])".equals(currentTab) &&
                           "setArrayListeners(ArrayListener[])".equals(targetName)) {
                     found = true;
                  }
                  else if ("Stack(int)".equals(currentTab) &&
                           "Stack(int)".equals(targetName)) {
                     found = true;
                  }
                  else if ("Stack(Stack)".equals(currentTab) &&
                           "Stack(Stack)".equals(targetName)) {
                     found = true;
                  }
                  else if ("push(Object)".equals(currentTab) &&
                           "push(java.lang.Object)".equals(targetName)) {
                     found = true;
                  }
                  else if ("pop()".equals(currentTab) &&
                           "pop()".equals(targetName)) {
                     found = true;
                  }
                  if (found) {
                     IDebugTarget target = launch.getDebugTarget();
                     toSelect.add(target);
                     if (target instanceof ISEDebugTarget) {
                        CollectionUtil.addAll(toSelect, ((ISEDebugTarget) target).getSymbolicThreads());
                     }
                     else {
                        CollectionUtil.addAll(toSelect, target.getThreads());
                     }
                  }
               }
            }
            if (!toSelect.isEmpty()) {
               Display.getDefault().asyncExec(new Runnable() {
                  @Override
                  public void run() {
                     IDebugView debugView = (IDebugView) WorkbenchUtil.getActivePage().findView(IDebugUIConstants.ID_DEBUG_VIEW);
                     if (debugView != null) {
                        Object currentSelected = SWTUtil.getFirstElement(debugView.getSite().getSelectionProvider().getSelection());
                        // Ensure that thread is selected, otherwise current selection is sticky, see AbstractSEDDebugNode#getAdapter() anonymous IModelSelectionPolicyFactory implementation
                        if (currentSelected instanceof IDebugElement) {
                           IDebugTarget currentTarget = ((IDebugElement) currentSelected).getDebugTarget();
                           debugView.getSite().getSelectionProvider().setSelection(SWTUtil.createSelection(currentTarget)); // Parent elements
                        }
                        // Select new targets
                        SEDUIUtil.selectInDebugView(debugView, debugView, toSelect);
                     }
                     else {
                        System.out.println("No debug view");
                     }
                  }
               });
            }
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
   }
}
