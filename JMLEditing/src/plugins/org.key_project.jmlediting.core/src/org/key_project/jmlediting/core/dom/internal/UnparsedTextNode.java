package org.key_project.jmlediting.core.dom.internal;

import org.key_project.jmlediting.core.dom.NodeTypes;

public class UnparsedTextNode extends StringNode {

   public UnparsedTextNode(final int startOffset, final int endOffset,
         final String string) {
      super(startOffset, endOffset, string);
   }

   @Override
   public int getType() {
      return NodeTypes.UNPARSED_TEXT;
   }

}
