package org.key_project.jmlediting.core.resolver.typecomputer;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.resolver.ResolverException;

public class TypeComputerException extends Exception {

   private static final long serialVersionUID = -5325964533644655328L;

   private final IASTNode node;

   public TypeComputerException(final String message, final IASTNode node) {
      super(message);
      this.node = node;
   }

   public TypeComputerException(final String string, final IASTNode node,
            final ResolverException e) {
      super(string, e);
      this.node = node;
   }

   public IASTNode getNode() {
      return node;
   }
}
