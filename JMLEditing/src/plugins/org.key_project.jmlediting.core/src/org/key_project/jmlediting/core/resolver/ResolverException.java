package org.key_project.jmlediting.core.resolver;

import org.key_project.jmlediting.core.dom.IASTNode;

/**
 * ResolverException is thrown, if the resolver can not read the IASTNode given. Or something
 * unexpected happens.
 * 
 * @author Christopher Beckmann
 *
 */
public class ResolverException extends Exception {

   /**
     * 
     */
   private static final long serialVersionUID = 585636674455840351L;
   private IASTNode node = null;

   /**
    * Creates a simple ResolverException without any additional data.
    * 
    * @param string the detail message.
    */
   public ResolverException(final String string) {
      super(string);
   }

   /**
    * Creates a simple ResolverException storing another Exception.
    * 
    * @param string the detail message.
    * @param e the cause that caused this Exception. {@code null} is accepted.
    */
   public ResolverException(final String string, final Throwable e) {
      super(string, e);
   }

   /**
    * Creates a ResolverException storing the {@link IASTNode} that was worked with and
    * another Exception.
    * 
    * @param string the detail message.
    * @param node the {@link IASTNode} that was worked with, when throwing the exception.
    * @param e the cause that caused this Exception. {@code null} is accepted.
    */
   public ResolverException(final String string, final IASTNode node, final Throwable e) {
      super(string, e);
      this.node = node;
   }

   /**
    * Returns the stored {@link IASTNode}. Can return {@code null}, if nothing has been saved.
    * 
    * @return the saved {@link IASTNode}. Can return {@code null}
    */
   public final IASTNode getNode() {
      return node;
   }
}
