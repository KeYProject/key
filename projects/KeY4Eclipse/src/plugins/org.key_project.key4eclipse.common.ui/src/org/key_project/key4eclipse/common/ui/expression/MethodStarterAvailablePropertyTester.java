package org.key_project.key4eclipse.common.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;

/**
 * A {@link PropertyTester} which checks if the global start functionality
 * via {@link IMethodStarter}s is available or not.
 * @author Martin Hentschel
 */
public class MethodStarterAvailablePropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      return StarterUtil.areMethodStartersAvailable();
   }
}
