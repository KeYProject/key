package org.key_project.sed.key.evaluation.model.tooling;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditorPreferenceConstants;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.SwingUtil;
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
   
   private final String methodSignature;
   
   private IPerspectiveDescriptor originalPerspective;
   
   private Proof proof;
   
   private ILaunchConfiguration launchConfiguration;
   
   private boolean originalShowLineNumbers;
   
   public ProofAttemptJavaProjectModifier(String typeName, 
                                          String methodName, 
                                          String[] methodParameters, 
                                          String methodSignature,
                                          FileDefinition proofFileDefinition, 
                                          FileDefinition... files) {
      super(ArrayUtil.add(files, proofFileDefinition));
      this.typeName = typeName;
      this.methodName = methodName;
      this.methodParameters = methodParameters;
      this.methodSignature = methodSignature;
      this.proofFileDefinition = proofFileDefinition;
   }

   @Override
   protected String getCompletionMessage() {
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

   @Override
   public synchronized String modifyWorkbench() throws Exception {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            originalShowLineNumbers = EditorsUI.getPreferenceStore().getBoolean(AbstractDecoratedTextEditorPreferenceConstants.EDITOR_LINE_NUMBER_RULER);
            EditorsUI.getPreferenceStore().setValue(AbstractDecoratedTextEditorPreferenceConstants.EDITOR_LINE_NUMBER_RULER, true);
         }
      });
      return super.modifyWorkbench();
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
                     MainWindow.getInstance().selectFirstTab();
                  }
               });
            }
            else if (UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME.equals(getTool().getName())) {
               // Open Symbolic Debug perspective
               getWorkbenchPage().setPerspective(WorkbenchUtil.getPerspectiveDescriptor(SymbolicDebugPerspectiveFactory.PERSPECTIVE_ID));
               // Launch proof in SED
               boolean launchSuccessful = false;
               while (!launchSuccessful) {
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
                  // Perform lazy side proofs to ensure fast tree rendering
                  ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
                  for (ILaunch launch : launchManager.getLaunches()) {
                     if (!launch.isTerminated() && launchConfiguration.equals(launch.getLaunchConfiguration())) {
                        launchSuccessful = true;
                        performLazyWork(launch);
                     }
                  }
               }
            }
         }
      }
   }

   protected void performLazyWork(ILaunch launch) {
      if (launch != null) {
         for (IDebugTarget target : launch.getDebugTargets()) {
            performLazyWork(target);
         }
      }
   }
   
   protected void performLazyWork(IDebugTarget target) {
      try {
         if (target instanceof ISEDDebugTarget) {
            for (ISEDThread thread : ((ISEDDebugTarget) target).getSymbolicThreads()) {
               try {
                  SEDPreorderIterator iterator = new SEDPreorderIterator(thread);
                  while (iterator.hasNext()) {
                     ISEDDebugElement next = iterator.next();
                     if (next instanceof ISEDDebugNode) {
                        ((ISEDDebugNode) next).getName(); // May performs side proofs
                     }
                  }
               }
               catch (DebugException e) {
                  // Nothing to do.
               }
            }
         }
      }
      catch (DebugException e) {
         // Nothing to do.
      }
   }

   @Override
   protected void doAdditinalCleanup() throws Exception {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            EditorsUI.getPreferenceStore().setValue(AbstractDecoratedTextEditorPreferenceConstants.EDITOR_LINE_NUMBER_RULER, originalShowLineNumbers);
         }
      });
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
               DebugPlugin.getDefault().getLaunchManager().removeLaunch(launch);
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
