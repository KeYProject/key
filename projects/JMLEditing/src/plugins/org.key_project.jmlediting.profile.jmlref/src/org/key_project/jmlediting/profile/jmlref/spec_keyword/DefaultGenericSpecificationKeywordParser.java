package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;

public class DefaultGenericSpecificationKeywordParser extends
AbstractGenericSpecificationKeywordParser {

   @Override
   protected IASTNode parseToSemicolon(final String text, final int start,
         final int end) {
      // Content without semicolon
      final String content = text.substring(start, end);
      // Cover the semicolon
      return Nodes.createNode(NodeTypes.NODE,
            Nodes.createString(start, end + 1, content));

   }

}
