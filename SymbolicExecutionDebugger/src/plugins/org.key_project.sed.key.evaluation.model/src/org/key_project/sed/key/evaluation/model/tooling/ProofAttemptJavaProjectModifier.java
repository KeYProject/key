package org.key_project.sed.key.evaluation.model.tooling;

import org.eclipse.core.resources.IFile;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.SwingUtil;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;

public class ProofAttemptJavaProjectModifier extends AbstractSEDJavaProjectModifier {
   private final FileDefinition proofFileDefinition;
   
   private final String typeName;
   
   private final String methodName;
   
   private final String[] methodParameters;
   
   private final String methodSignature;
   
   private IPerspectiveDescriptor originalPerspective;
   
   private Proof proof;
   
   private ILaunchConfiguration launchConfiguration;
   
   private final boolean showCompletionMessage;
   
   public ProofAttemptJavaProjectModifier(String typeName, 
                                          String methodName, 
                                          String[] methodParameters, 
                                          String methodSignature,
                                          boolean showCompletionMessage,
                                          FileDefinition proofFileDefinition, 
                                          FileDefinition... files) {
      super(ArrayUtil.add(files, proofFileDefinition));
      this.typeName = typeName;
      this.methodName = methodName;
      this.methodParameters = methodParameters;
      this.methodSignature = methodSignature;
      this.showCompletionMessage = showCompletionMessage;
      this.proofFileDefinition = proofFileDefinition;
   }

   @Override
   protected String getCompletionMessage() {
      if (showCompletionMessage) {
         if (UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME.equals(getTool().getName())) {
            return "The proof attempt of '" + typeName + "#" + methodSignature + "' is shown in KeY (separate window). " +
                   "The corresponding source code is shown in Eclipse (active editor).\n\n" +
                   "Please answer the questions shown in the evaluation wizard.\n" +
                   "Do NOT open the proof attempt with SED!";
         }
         else if (UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME.equals(getTool().getName())) {
            return "The symbolic execution tree of the proof attempt of '" + typeName + "#" + methodSignature + "' is shown in Eclipse. " +
                   "The corresponding source code is shown in the active editor.\n\n" +
                   "Please answer the questions shown in the evaluation wizard.\n" +
                   "Do NOT open the proof attempt with KeY!";
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
   protected void fileCreated(FileDefinition definition, final IFile projectFile) throws Exception {
      super.fileCreated(definition, projectFile);
      if (getTool() != null) {
         if (ObjectUtil.equals(proofFileDefinition, definition)) {
            originalPerspective = getWorkbenchPage().getPerspective();
            if (UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME.equals(getTool().getName())) {
               getWorkbenchPage().setPerspective(WorkbenchUtil.getPerspectiveDescriptor("org.eclipse.jdt.ui.JavaPerspective"));
               MainWindow.getInstance().setVisible(true);
               MainWindow.getInstance().toFront();
               AbstractProblemLoader loader = MainWindow.getInstance().getUserInterface().load(null,
                                                                                               ResourceUtil.getLocation(projectFile),
                                                                                               KeYResourceProperties.getKeYClassPathEntries(projectFile.getProject()),
                                                                                               KeYResourceProperties.getKeYBootClassPathLocation(projectFile.getProject()),
                                                                                               KeYResourceProperties.getKeYIncludes(projectFile.getProject()), null, false);
               proof = loader.getProof();
               // Ensure that tab proof is selected.
               SwingUtil.invokeLater(new Runnable() {
                  @Override
                  public void run() {
                     MainWindow.getInstance().setShowTacletInfo(true);
                     MainWindow.getInstance().selectFirstTab();
                  }
               });
            }
            else if (UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME.equals(getTool().getName())) {
               // Open Symbolic Debug perspective
               getWorkbenchPage().setPerspective(WorkbenchUtil.getPerspectiveDescriptor(SymbolicDebugPerspectiveFactory.PERSPECTIVE_ID));
               // Launch
               launchConfiguration = launchSED(typeName, methodName, methodParameters, projectFile);
            }
         }
      }
   }

   @Override
   protected void doAdditinalCleanup() throws Exception {
      super.doAdditinalCleanup();
      if (proof != null) {
         proof.dispose();
         MainWindow.getInstance().setVisible(false);
         proof = null;
      }
      terminate(launchConfiguration);
      if (originalPerspective != null) {
         Display.getDefault().syncExec(new Runnable() {
            @Override
            public void run() {
               getWorkbenchPage().setPerspective(originalPerspective);
            }
         });
      }
   }
}
