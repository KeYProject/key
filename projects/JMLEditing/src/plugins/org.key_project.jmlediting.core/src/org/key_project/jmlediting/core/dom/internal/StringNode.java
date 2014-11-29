package org.key_project.jmlediting.core.dom.internal;

import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;

public class StringNode extends PrimitiveNode implements IStringNode {

   private String string;
   
   public StringNode(int startOffset, int endOffset, String string) {
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

}
