package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import static org.key_project.jmlediting.core.parser.LexicalHelper.scanForClosingSemicolon;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

public abstract class AbstractGenericSpecificationKeywordParser implements
IKeywordParser {

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      final int closingSemicolon = scanForClosingSemicolon(text, start, end);

      try {
         final IASTNode contentResult = this.parseToSemicolon(text, start + 1,

               closingSemicolon);
         return Nodes.createNode(contentResult.getStartOffset(),
               closingSemicolon + 1, NodeTypes.KEYWORD_CONTENT, contentResult);
      }
      catch (final ParserException e) {
         final IASTNode errorNode = e.getErrorNode();
         if (errorNode != null) {
            // Parser was able to recover, so we do not need to insert an error
            // node
            throw new ParserException(e, Nodes.createNode(
                  errorNode.getStartOffset(), closingSemicolon + 1,
                  NodeTypes.KEYWORD_CONTENT, errorNode));
         }
         // There is no result, so we add the complete content as an error node
         throw new ParserException(e, Nodes.createNode(start + 1,
               closingSemicolon + 1, NodeTypes.KEYWORD_CONTENT, Nodes
               .createErrorNode(Nodes.createUnparsedTextNode(
                     text.substring(start + 1, closingSemicolon),
                     start + 1, closingSemicolon))));
      }

   }

   @Override
   public void setProfile(final IJMLProfile profile) {
      // By default most do not need them, if they, they should override
      // explicitly
   }

   protected abstract IASTNode parseToSemicolon(String text, int start, int end)
         throws ParserException;

}
