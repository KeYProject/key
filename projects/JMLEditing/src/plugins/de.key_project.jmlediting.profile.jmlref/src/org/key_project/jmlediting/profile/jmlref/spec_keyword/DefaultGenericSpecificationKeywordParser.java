package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;

public class DefaultGenericSpecificationKeywordParser extends
      AbstractGenericSpecificationKeywordParser {

   @Override
   protected IASTNode parseToSemicolon(String text, int start, int end) {
   // Content without semicolon
      String content = text.substring(start, end);
      return Nodes.createNode(NodeTypes.NODE, Nodes.createString(start, end, content));
      
   }

}
