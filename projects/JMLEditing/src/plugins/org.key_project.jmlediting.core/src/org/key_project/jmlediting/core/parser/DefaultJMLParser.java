package org.key_project.jmlediting.core.parser;

import static org.key_project.jmlediting.core.parser.LexicalHelper.skipLayout;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.internal.ParserUtils;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.ToplevelKeywordSort;
import org.key_project.jmlediting.core.utilities.CommentRange;

/**
 * The default implementation for an JML Parser with respect to the keywords
 * supported in an {@link IJMLProfile}. This parser searches for a keyword, then
 * calls the parser for the keyword to continue parsing. Then the parser
 * continues with searching for an keyword.
 *
 * @author Moritz Lichter
 *
 */
public class DefaultJMLParser implements IJMLParser {

   /**
    * The profile to use to parse.
    */
   private final IJMLProfile profile;

   /**
    * Creates an new {@link DefaultJMLParser} for the given profile.
    *
    * @param profile
    *           the profile with the supported keywords, not allowed to be null
    */
   public DefaultJMLParser(final IJMLProfile profile) {
      if (profile == null) {
         throw new IllegalArgumentException("Cannot pass a null profile");
      }
      this.profile = profile;
   }

   @Override
   public IASTNode parse(final String text, final CommentRange range)
         throws ParserException {
      // End offset is inclusive, but parse takes an exclusive context
      return this.parse(text, range.getContentBeginOffset(),
            range.getContentEndOffset() + 1);
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      ParserUtils.validatePositions(text, start, end);

      // A list to put the nodes for each keyword into
      final List<IASTNode> allKeywords = new ArrayList<IASTNode>();

      final List<ParserError> keywordErrors = new ArrayList<ParserError>();

      int position = skipLayout(text, start, end, true);

      // Whether there is a parse error in the current node
      boolean error = false;
      // Whether there was an error in the last node
      boolean lastError = false;

      // Search for keyword as long text is available
      while (position < end) {
         // Parse the keyword

         IASTNode keywordNode;

         try {
            keywordNode = ParserUtils.parseKeyword(text, position,

            end, JMLProfileHelper.filterKeywords(this.profile,
                  ToplevelKeywordSort.INSTANCE), this.profile);

            error = false;
         }
         catch (final ParserException e) {
            keywordNode = e.getErrorNode();
            // Collect all errors
            keywordErrors.addAll(e.getAllErrors());
            error = true;
            if (keywordNode == null) {
               // Was not able to find any keyword, skip text until next
               // whitespace because this token is not parseable
               // This is faster than just removing one char at one
               // First determine where unparseable keyword starts
               final int textStart = skipLayout(text, position, end);
               // Then skip until the next whitespace from there
               int nextPosition;
               try {
                  nextPosition = LexicalHelper.findNextWhitespace(text,
                        textStart, end);
                  nextPosition = skipLayout(text, nextPosition, end, false);
               }
               catch (final ParserException e2) {
                  // No whitespace anymore, so take rest of the text
                  nextPosition = end;
               }
               // Ignore this token for a keyword and continue with the rest
               keywordNode = Nodes.createErrorNode(Nodes
                     .createUnparsedTextNode(
                           text.substring(textStart, nextPosition), textStart,
                           nextPosition));
               position = nextPosition;
            }

         }
         if (lastError) {
            // The last node contains a parse error
            // We want to contain all characters until the start of the current
            // node to the last node
            // Because the node could not be parsed completly
            final IASTNode lastErrorNode = allKeywords
                  .get(allKeywords.size() - 1);
            final IASTNode newErrorNode = Nodes.createNode(
                  lastErrorNode.getStartOffset(), keywordNode.getStartOffset(),
                  lastErrorNode.getType(), lastErrorNode.getChildren());
            allKeywords.set(allKeywords.size() - 1, newErrorNode);
         }
         allKeywords.add(keywordNode);
         // Skip whites
         position = keywordNode.getEndOffset();
         if (position < end) {
            position = skipLayout(text, position, end, false);
         }
         lastError = error;
      }

      // It is required to find at least something
      if (allKeywords.size() == 0) {
         throw new ParserException("Nothing specified", text, start);
      }

      final IASTNode finalNode = Nodes.createNode(NodeTypes.NODE, allKeywords);
      if (keywordErrors.isEmpty()) {
         return finalNode;
      }
      else {
         throw new ParserException(null, keywordErrors, text, finalNode, null);
      }
   }

}
