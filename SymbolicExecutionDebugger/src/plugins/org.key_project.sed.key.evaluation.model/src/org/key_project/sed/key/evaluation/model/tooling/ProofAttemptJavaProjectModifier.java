package org.key_project.sed.key.evaluation.model.tooling;

import org.eclipse.core.internal.jobs.JobManager;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.util.eclipse.JobUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;


@SuppressWarnings("restriction")
public class ProofAttemptJavaProjectModifier extends JavaProjectModifier {
   private final FileDefinition proofFileDefinition;
   
   private final String typeName;
   
   private final String methodName;
   
   private final String[] methodParameters;
   
   private IPerspectiveDescriptor originalPerspective;
   
   private Proof proof;
   
   private ILaunchConfiguration launchConfiguration;
   
   public ProofAttemptJavaProjectModifier(String typeName, 
                                          String methodName, 
                                          String[] methodParameters, 
                                          FileDefinition proofFileDefinition, 
                                          FileDefinition... files) {
      super(ArrayUtil.add(files, proofFileDefinition));
      this.typeName = typeName;
      this.methodName = methodName;
      this.methodParameters = methodParameters;
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
                        IType type = getJavaProject().findType(typeName);
                        IMethod method = type != null ?
                                         type.getMethod(methodName, methodParameters) : 
                                         null;
                        launchConfiguration = KeySEDUtil.createConfiguration(projectFile, method);
                        launchConfiguration = KeySEDUtil.updateLaunchConfiguration(launchConfiguration, null, null, true, true, false, false, false, true, true, true, true);
                        DebugUIPlugin.launchInForeground(launchConfiguration, KeySEDUtil.MODE);
                        // TODO: Wait for jobs like synchronization which throws exceptions otherwise
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
         MainWindow.getInstance().setVisible(false);
         proof = null;
      }
      if (launchConfiguration != null) {
         ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
         for (ILaunch launch : launchManager.getLaunches()) {
            if (launchConfiguration.equals(launch.getLaunchConfiguration())) {
               launch.terminate();
            }
         }
         launchConfiguration.delete();
         launchConfiguration = null;
      }
      if (originalPerspective != null) {
         getWorkbenchPage().setPerspective(originalPerspective);
      }
   }
}
