package org.key_project.sed.key.evaluation.model.tooling;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.sed.key.evaluation.model.Activator;
import org.key_project.sed.key.evaluation.model.definition.ReviewingCodeEvaluation;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

public class ReviewingCodeJavaProjectModifier extends AbstractSEDJavaProjectModifier {
   private final String typeName;
   
   private final ProofFileFileDefinition[] proofFileDefinitions;
   
   private final FileDefinition bootClassPathDefinition;
   
   private IPerspectiveDescriptor originalPerspective;
   
   private final boolean showCompletionMessage;
   
   private final List<ILaunchConfiguration> launchConfigurations = new LinkedList<ILaunchConfiguration>();
   
   public ReviewingCodeJavaProjectModifier(String typeName,
                                           boolean showCompletionMessage,
                                           FileDefinition bootClassPathDefinition,
                                           ProofFileFileDefinition[] proofFileDefinitions, 
                                           FileDefinition... files) {
      super(files);
      this.typeName = typeName;
      this.bootClassPathDefinition = bootClassPathDefinition;
      this.showCompletionMessage = showCompletionMessage;
      this.proofFileDefinitions = proofFileDefinitions;
   }

   @Override
   protected String getCompletionMessage() {
      if (showCompletionMessage) {
         if (ReviewingCodeEvaluation.NO_TOOL_NAME.equals(getTool().getName())) {
            return "The source code of '" + typeName + "' is shown in Eclipse.\n" +
                   "Please answer the questions shown in the evaluation wizard.\n" +
                   "Do NOT symbolically execute the source code using SED!";
         }
         else if (ReviewingCodeEvaluation.SED_TOOL_NAME.equals(getTool().getName())) {
            return "The symbolic execution tree of the source code of '" + typeName + "' is shown in Eclipse.\n" +
                   "Please answer the questions shown in the evaluation wizard.\n" +
                   "Do not execute or debug the source code using JDT!";
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
}
