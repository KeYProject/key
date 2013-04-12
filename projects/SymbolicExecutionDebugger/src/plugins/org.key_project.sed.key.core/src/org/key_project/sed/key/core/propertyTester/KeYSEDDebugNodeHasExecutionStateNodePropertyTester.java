package org.key_project.sed.key.core.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.util.java.ArrayUtil;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;

/**
 * This property tester can be used to make sure that an {@link IKeYSEDDebugNode} 
 * contains an {@link IExecutionStateNode}. 
 * @author Martin Hentschel
 */
public class KeYSEDDebugNodeHasExecutionStateNodePropertyTester extends PropertyTester {
   /**
    * Argument to verify also that the {@link IKeYSEDDebugNode} is not disposed.
    */
   public static final String NOT_DISPOSED_ARGUMENT = "notDisposed";

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, 
                       String property, 
                       Object[] args, 
                       Object expectedValue) {
      if (receiver instanceof IKeYSEDDebugNode<?>) {
         IExecutionNode node = ((IKeYSEDDebugNode<?>)receiver).getExecutionNode();
         if (ArrayUtil.contains(args, NOT_DISPOSED_ARGUMENT)) {
            return node instanceof IExecutionStateNode<?> && !node.isDisposed();
         }
         else {
            return node instanceof IExecutionStateNode<?>;
         }
      }
      else {
         return false;
      }
   }
}
