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
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.util.SEPreorderIterator;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

@SuppressWarnings("restriction")
public abstract class AbstractSEDJavaProjectModifier extends JavaProjectModifier {
   public AbstractSEDJavaProjectModifier(FileDefinition... files) {
      super(files);
   }
   
   protected ILaunchConfiguration launchSED(final String typeName, 
                                            final String methodName, 
                                            final String[] methodParameters,
                                            final IFile projectFile) throws Exception {
      // Launch proof in SED
      ILaunchConfiguration launchConfiguration = null;
      boolean launchSuccessful = false;
      while (!launchSuccessful) {
         IRunnableWithResult<ILaunchConfiguration> run = new AbstractRunnableWithResult<ILaunchConfiguration>() {
            @Override
            public void run() {
               try {
                  IType type = getJavaProject().findType(typeName);
                  IMethod method = type != null ?
                                   type.getMethod(methodName, methodParameters) : 
                                   null;
                  ILaunchConfiguration launchConfiguration = KeySEDUtil.createConfiguration(projectFile, method);
                  setResult(launchConfiguration);
                  launchConfiguration = KeySEDUtil.updateLaunchConfiguration(launchConfiguration, null, null, true, true, false, false, false, true, true, true, true, areVariablesAreComputedFromUpdates());
                  DebugUIPlugin.launchInForeground(launchConfiguration, KeySEDUtil.MODE);
               }
               catch (CoreException e) {
                  setException(e);
               }
            }
         };
         getShell().getDisplay().syncExec(run);
         launchConfiguration = run.getResult();
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
      return launchConfiguration;
   }

   protected Boolean areVariablesAreComputedFromUpdates() {
      return null;
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
         if (target instanceof ISEDebugTarget) {
            for (ISEThread thread : ((ISEDebugTarget) target).getSymbolicThreads()) {
               try {
                  SEPreorderIterator iterator = new SEPreorderIterator(thread);
                  while (iterator.hasNext()) {
                     ISEDebugElement next = iterator.next();
                     if (next instanceof ISENode) {
                        ((ISENode) next).getName(); // May performs side proofs
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
   
   protected void terminate(ILaunchConfiguration launchConfiguration) throws Exception {
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
   }
}
