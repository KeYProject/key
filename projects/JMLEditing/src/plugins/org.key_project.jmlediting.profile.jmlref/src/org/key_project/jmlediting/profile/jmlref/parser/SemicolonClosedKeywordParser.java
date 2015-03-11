package org.key_project.jmlediting.profile.jmlref.parser;

import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;

/**
 * Specialized the {@link ParseFunctionKeywordParser} for the content of generic
 * keywords. This parser adds the closing ; to the {@link ParseFunction}
 * provided by subclasses.
 *
 * @author Moritz Lichter
 *
 */
public abstract class SemicolonClosedKeywordParser extends
      JMLRefParseFunctionKeywordParser {

   /**
    * Returns the parse function for the content of the parser without the ;.
    *
    * @param profile
    *           the profile to parse according to
    * @return the parse function for the profile
    */
   protected abstract ParseFunction createContentParseFunction(
         final IJMLExpressionProfile profile);

   @Override
   protected ParseFunction createParseFunction(
         final IJMLExpressionProfile profile) {
      return ParserBuilder.closedBy(NodeTypes.KEYWORD_CONTENT,
            this.createContentParseFunction(profile), ';');
   }

}
