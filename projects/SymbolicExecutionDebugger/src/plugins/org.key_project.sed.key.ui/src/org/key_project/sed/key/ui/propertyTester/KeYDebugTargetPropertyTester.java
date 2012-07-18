package org.key_project.sed.key.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.key_project.sed.key.core.model.KeYDebugTarget;

/**
 * This property tester can be used to make sure that an {@link ILaunch} 
 * contains exactly one {@link KeYDebugTarget} and that {@link IDebugElement}s
 * are contained in a {@link KeYDebugTarget}, 
 * @author Martin Hentschel
 */
public class KeYDebugTargetPropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, 
                       String property, 
                       Object[] args, 
                       Object expectedValue) {
      boolean singleKeYDebugTarget = false;
      if (receiver instanceof ILaunch) {
         ILaunch launch = (ILaunch)receiver;
         if (launch.getDebugTargets() != null && 
             launch.getDebugTargets().length == 1 && 
             launch.getDebugTargets()[0] instanceof KeYDebugTarget) {
            singleKeYDebugTarget = true;
         }
      }
      else if (receiver instanceof IDebugElement)  {
         IDebugElement element = (IDebugElement)receiver;
         if (element.getDebugTarget() instanceof KeYDebugTarget) {
            singleKeYDebugTarget = true;
         }
      }
      return singleKeYDebugTarget;
   }
}
