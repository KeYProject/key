package org.key_project.jmlediting.core.dom.internal;

import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;

/**
 * A {@link StringNode} is a primitive node just containing a string.
 *
 * @author Moritz Lichter
 *
 */
public class StringNode extends PrimitiveNode implements IStringNode {

   /**
    * The content of the node.
    */
   private final String string;

   /**
    * Creates a new {@link StringNode}.
    *
    * @param startOffset
    *           the start offset
    * @param endOffset
    *           the end offset
    * @param string
    *           the string content of the node
    */
   public StringNode(final int startOffset, final int endOffset,
         final String string) {
      super(startOffset, endOffset);
      this.string = string;
   }

   @Override
   public int getType() {
      return NodeTypes.STRING;
   }

   @Override
   public String getString() {
      return this.string;
   }

   @Override
   public String toString() {
      return NodeTypes.getTypeName(this.getType()) + "["
            + this.getStartOffset() + "-" + this.getEndOffset() + "]("
            + this.string + ")";
   }

   @Override
   public String prettyPrintAST() {
      return "\"" + this.string + "\"";
   }

}
