package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.Nodes;

/**
 * A default implementation for method specification keywords. The content of
 * the keyword is the text after the keyword to a closing semicolon which is not
 * parsed further.
 *
 * @author Moritz Lichter
 *
 */
public class DefaultGenericSpecificationKeywordParser extends
      AbstractGenericSpecificationKeywordParser {

   @Override
   protected IASTNode parseToSemicolon(final String text, final int start,
         final int end) {
      // Content without semicolon
      final String content = text.substring(start, end);
      return Nodes.createString(start, end, content);

   }

}
