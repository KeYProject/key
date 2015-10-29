package org.key_project.jmlediting.core.resolver.typecomputer;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.resolver.ResolverException;

/**
 * The TypeComputerExcpetion is thrown, when the {@link TypeComputer} can not process a given {@link IASTNode}.
 * @author Christopher Beckmann
 *
 */
public class TypeComputerException extends Exception {

   private static final long serialVersionUID = -5325964533644655328L;

   private final IASTNode node;

   /** Creates a TypeComputerException with given message and node.
    * 
    * @param message the reason that caused the exception
    * @param node the {@link IASTNode} that was used when the exception occurred
    */
   public TypeComputerException(final String message, final IASTNode node) {
      super(message);
      this.node = node;
   }

   /** Created a TypeComputerException with a given message, node and exception that might have caused this one to occur.
    * 
    * @param string the reason that caused the exception
    * @param node the {@link IASTNode} that was used when the exception occurred
    * @param e the exception that caused this exception to occur
    */
   public TypeComputerException(final String string, final IASTNode node,
            final ResolverException e) {
      super(string, e);
      this.node = node;
   }

   /**
    * Get the {@link IASTNode} that caused this Exception.
    * @return the saved {@link IASTNode} can be {@code null}
    */
   public IASTNode getNode() {
      return node;
   }
}
