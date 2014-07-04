package org.key_project.sed.ui.visualization.execution_tree.command;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.visualization.execution_tree.wizard.SaveSetAsWizard;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * Opens the {@link SaveSetAsWizard} for selected {@link ILaunch}s to save
 * them as SET file.
 * @author Martin Hentschel
 */
public class SaveSetAsCommand extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      Object[] selection = SWTUtil.toArray(HandlerUtil.getCurrentSelection(event));
      List<ISEDDebugTarget> targets = new LinkedList<ISEDDebugTarget>();
      for (Object obj : selection) {
         if (obj instanceof ILaunch) {
            IDebugTarget[] launchTargets = ((ILaunch) obj).getDebugTargets();
            for (IDebugTarget target : launchTargets) {
               if (target instanceof ISEDDebugTarget) {
                  targets.add((ISEDDebugTarget)target);
               }
            }
         }
         else if (obj instanceof ISEDDebugTarget) {
            targets.add((ISEDDebugTarget)obj);
         }
         else if (obj instanceof IDebugElement) {
            IDebugTarget target = ((IDebugElement) obj).getDebugTarget();
            if (target instanceof ISEDDebugTarget) {
               targets.add((ISEDDebugTarget)target);
            }
         }
         SaveSetAsWizard.openWizard(HandlerUtil.getActiveShell(event),  
                                    HandlerUtil.getActiveWorkbenchWindow(event),
                                    targets.toArray(new ISEDDebugTarget[targets.size()]));
      }
      return null;
   }
}
