package org.key_project.sed.key.evaluation.model.tooling;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.ui.launch.KeYLaunchShortcut;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;


public class ProofAttemptJavaProjectModifier extends JavaProjectModifier {
   private final FileDefinition proofFileDefinition;
   
   private IPerspectiveDescriptor originalPerspective;
   
   private Proof proof;
   
   private ILaunchConfiguration launchConfiguration;
   
   public ProofAttemptJavaProjectModifier(FileDefinition proofFileDefinition, FileDefinition... files) {
      super(ArrayUtil.add(files, proofFileDefinition));
      this.proofFileDefinition = proofFileDefinition;
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
            }
            else if (UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME.equals(getTool().getName())) {
               getWorkbenchPage().setPerspective(WorkbenchUtil.getPerspectiveDescriptor(SymbolicDebugPerspectiveFactory.PERSPECTIVE_ID));
               IRunnableWithException run = new AbstractRunnableWithException() {
                  @Override
                  public void run() {
                     try {
                        launchConfiguration = KeYLaunchShortcut.launch(projectFile, null, KeySEDUtil.MODE);
                     }
                     catch (CoreException e) {
                        setException(e);
                     }
                  }
               };
               getShell().getDisplay().syncExec(run);
               if (run.getException() != null) {
                  throw run.getException();
               }
            }
         }
      }
   }

   @Override
   protected void doAdditinalCleanup() throws Exception {
      super.doAdditinalCleanup();
      if (proof != null) {
         proof.dispose();
         proof = null;
      }
      if (launchConfiguration != null) {
         ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
         for (ILaunch launch : launchManager.getLaunches()) {
            if (launchConfiguration.equals(launch.getLaunchConfiguration())) {
               launch.terminate();
            }
         }
         launchConfiguration = null;
      }
      if (originalPerspective != null) {
         getWorkbenchPage().setPerspective(originalPerspective);
      }
   }
}
