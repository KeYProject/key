package org.key_project.jmlediting.core.parser;

import static org.key_project.jmlediting.core.parser.LexicalHelper.skipWhiteSpacesOrAt;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.iternal.ParserUtilsImpl;
import org.key_project.jmlediting.core.profile.IJMLProfile;

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

      int position = skipWhiteSpacesOrAt(text, start, end, true);
      // Search for keyword as long text is available
      while (position < end) {
         // Parse the keyword
         final IASTNode keywordNode = ParserUtilsImpl
               .parseKeyword(text, position, end,
                     this.profile.getSupportedKeywords(), this.profile);
         allKeywords.add(keywordNode);
         // Skip whites
         position = keywordNode.getEndOffset();
         if (position < end) {
            position = skipWhiteSpacesOrAt(text, position, end, false);
         }
      }

      // It is required to find at least something
      if (allKeywords.size() == 0) {
         throw new ParserException("Nothing specified", text, start);
      }

      return Nodes.createNode(NodeTypes.NODE, allKeywords);
   }

}
