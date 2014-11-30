package org.key_project.jmlediting.core.dom.internal;

import java.util.Collections;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;

/**
 * An ASTNode implements a default AST node.
 *
 * @author Moritz Lichter
 *
 */
public class ASTNode extends AbstractASTNode {

   /**
    * The type of the node.
    */
   private final int type;
   /**
    * The list of all children.
    */
   private final List<IASTNode> children;

   /**
    * Creates a new {@link ASTNode}. The start offset needs to be less than or
    * equal to the end offset.
    *
    * @param startOffset
    *           the start offset
    * @param endOffset
    *           the end offset
    * @param type
    *           the type of the node
    * @param children
    *           the list of children of the node, may be null
    */
   public ASTNode(final int startOffset, final int endOffset, final int type,
         final List<IASTNode> children) {
      super(startOffset, endOffset);
      this.type = type;
      this.children = children;
   }

   @Override
   public int getType() {
      return this.type;
   }

   @Override
   public List<IASTNode> getChildren() {
      // We need to return a non null list in any case
      if (this.children == null) {
         return Collections.emptyList();
      }
      else {
         return Collections.unmodifiableList(this.children);
      }
   }

}
