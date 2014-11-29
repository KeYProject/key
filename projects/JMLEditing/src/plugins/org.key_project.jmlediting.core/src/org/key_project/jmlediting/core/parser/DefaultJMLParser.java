package org.key_project.jmlediting.core.parser;

import static org.key_project.jmlediting.core.parser.LexicalHelper.getIdentifier;
import static org.key_project.jmlediting.core.parser.LexicalHelper.skipWhiteSpacesOrAt;
import static org.key_project.jmlediting.core.parser.ParserUtils.validatePositions;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

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
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      ParserUtils.validatePositions(text, start, end);

      // A list to put the nodes for each keyword into
      final List<IASTNode> allKeywords = new ArrayList<IASTNode>();

      int position = skipWhiteSpacesOrAt(text, start, end);
      // Search for keyword as long text is available
      while (position < end) {
         // Parse the keyword
         final IASTNode keywordNode = this.parseKeyword(text, position, end);
         allKeywords.add(keywordNode);
         // Skip whites
         position = keywordNode.getEndOffset() + 1;
         if (position < end) {
            position = skipWhiteSpacesOrAt(text, position, end);
         }
      }

      // It is required to find at least something
      if (allKeywords.size() == 0) {
         throw new ParserException("Nothing specified", text, start);
      }

      return Nodes.createNode(NodeTypes.NODE, allKeywords);
   }

   /**
    * Parses the a single keyword and the rest specified by the parser of the
    * keyword.
    *
    * @param text
    *           the text to parse in
    * @param start
    *           the start position (the position for the next keywords)
    * @param end
    *           the maximum position (exclusive)
    * @return an IAST node for the keyword
    * @throws ParserException
    *            when parsing in not successful
    */
   private IASTNode parseKeyword(final String text, final int start,
         final int end) throws ParserException {
      validatePositions(text, start, end);

      // Find keyword in text
      final int keywordStart = skipWhiteSpacesOrAt(text, start, end);
      final int keywordEnd = getIdentifier(text, keywordStart, end);
      final String keyword = text.substring(keywordStart, keywordEnd);

      // Find the corresponding IKeyword instance from the profile
      IKeyword foundKeyword = null;
      for (final IKeyword availableKeyword : this.profile
            .getSupportedKeywords()) {
         if (availableKeyword.getKeywords().contains(keyword)) {
            foundKeyword = availableKeyword;
            break;
         }
      }
      if (foundKeyword == null) {
         throw new ParserException(
               "Not a supported specification statement keyword: \"" + keyword
                     + "\"", text, keywordEnd);
      }
      final IASTNode keywordNode = Nodes.createKeyword(keywordStart,
            keywordEnd, foundKeyword, keyword);

      // Now parse according to the keywword
      final IKeywordParser keywordParser = foundKeyword.createParser();
      final IASTNode keywordResult = keywordParser.parse(text, keywordEnd, end);

      // Build the result
      if (keywordResult == null) {
         return keywordNode;
      }
      else {
         return Nodes.createNode(NodeTypes.KEYWORD_APPL, keywordNode,
               keywordResult);
      }
   }

}
