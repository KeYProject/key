package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.LexicalHelper;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

/**
 * A default parser for the content of method specification keyword. It scans
 * the given text for the closing semicolon and calls a parser for that string.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractGenericSpecificationKeywordParser implements
      IKeywordParser {

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      // Scan for the semicolon
      final int closingSemicolon = LexicalHelper.scanForClosingCharacter(';',
            text, start, end);

      // Now parse that
      try {
         final IASTNode contentResult = this.parseToSemicolon(text, start + 1,

         closingSemicolon);
         return Nodes.createNode(contentResult.getStartOffset(),
               closingSemicolon + 1, NodeTypes.KEYWORD_CONTENT, contentResult);
      }
      catch (final ParserException e) {
         // Does not work, do error recovery
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

   /**
    * Parses the content to the closing semicolon.
    *
    * @param text
    *           the text to parse
    * @param start
    *           the start index
    * @param end
    *           the end index (the semicolon)
    * @return the result {@link IASTNode}
    * @throws ParserException
    *            an exception if parsing was not successful
    */
   protected abstract IASTNode parseToSemicolon(String text, int start, int end)
         throws ParserException;

}
