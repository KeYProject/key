package org.key_project.jmlediting.profile.key.other;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.LexicalHelper;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

/**
 * Implementation of the Key \dl_ dynamic logic keyword.
 *
 * @author Moritz Lichter
 *
 */
public class DynamicLogicPrimary implements IJMLPrimary {

   /**
    * private class for the \dl_ keyword part to get syntax highlighting.
    *
    * @author Moritz Lichter
    *
    */
   private static final class DLKeyword extends AbstractEmptyKeyword {

      /**
       * Only instances in this class.
       */
      private DLKeyword() {
         super(getKeyword());
      }

      @Override
      public String getDescription() {
         return null;
      }

      @Override
      public IKeywordSort getSort() {
         return null;
      }

      /**
       *
       * @return the \dl_ prefix
       */
      private static String getKeyword() {
         return "\\dl_";
      }

   }

   /**
    * Shared instance for the \dl_ keyword.
    */
   private static final DLKeyword DL_KEYWORD = new DLKeyword();
   /**
    * Current profile to parse for.
    */
   private IJMLExpressionProfile profile;

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      final int keywordBegin = LexicalHelper.skipLayout(text, start, end);
      final int keywordLength = DLKeyword.getKeyword().length();
      // Check for the beginning \dl_
      if (end - keywordBegin < keywordLength
            || !text.subSequence(keywordBegin, keywordBegin + keywordLength)
                  .equals(DLKeyword.getKeyword())) {
         throw new ParserException(
               "Requires \\dl_ for introducing dynamic logic", text,
               keywordBegin);
      }
      // Get the following identifier without whitespaces
      final int identifierStart = keywordBegin + keywordLength;
      final int identifierEnd = LexicalHelper.getIdentifier(text,
            identifierStart, end);

      // Parse the rest
      final ParseFunction rest = brackets(opt(new ExpressionParser(this.profile)
            .exprList()));

      final IASTNode dlcontent = rest.parse(text, identifierEnd, end);

      // Create the nodes
      final IASTNode keywordNode = Nodes.createKeyword(keywordBegin,
            identifierStart, DL_KEYWORD, DLKeyword.getKeyword());
      final IASTNode identifier = Nodes.createString(identifierStart,
            identifierEnd, text.substring(identifierStart, identifierEnd));
      final IASTNode content = Nodes.createNode(identifierStart,
            dlcontent.getEndOffset(), NodeTypes.KEYWORD_CONTENT, identifier,
            dlcontent);
      final IASTNode keywordAppl = Nodes.createNode(NodeTypes.KEYWORD_APPL,
            keywordNode, content);
      return keywordAppl;
   }

   @Override
   public void setProfile(final IJMLExpressionProfile profile) {
      this.profile = profile;
   }

}
