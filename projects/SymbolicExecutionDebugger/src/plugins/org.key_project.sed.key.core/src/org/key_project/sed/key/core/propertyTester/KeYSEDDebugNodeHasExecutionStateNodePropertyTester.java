package org.key_project.sed.key.core.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;

/**
 * This property tester can be used to make sure that an {@link IKeYSEDDebugNode} 
 * contains an {@link IExecutionStateNode}. 
 * @author Martin Hentschel
 */
public class KeYSEDDebugNodeHasExecutionStateNodePropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, 
                       String property, 
                       Object[] args, 
                       Object expectedValue) {
      if (receiver instanceof IKeYSEDDebugNode<?>) {
         return ((IKeYSEDDebugNode<?>)receiver).getExecutionNode() instanceof IExecutionStateNode<?>;
      }
      else {
         return false;
      }
   }
}
