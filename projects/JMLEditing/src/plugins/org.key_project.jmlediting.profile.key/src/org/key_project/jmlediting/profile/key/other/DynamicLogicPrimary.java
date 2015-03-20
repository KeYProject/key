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

public class DynamicLogicPrimary implements IJMLPrimary {

   private static class DL_Keyword extends AbstractEmptyKeyword {

      public DL_Keyword() {
         super("\\dl_");
      }

      @Override
      public String getDescription() {
         return null;
      }

      @Override
      public IKeywordSort getSort() {
         return null;
      }

   }

   private static DL_Keyword keyword = new DL_Keyword();
   private IJMLExpressionProfile profile;

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      final int keywordBegin = LexicalHelper.skipWhiteSpacesOrAt(text, start,
            end);
      // Check for the beginning \dl_
      if (end - keywordBegin < 4
            || !text.subSequence(keywordBegin, keywordBegin + 4)
                  .equals("\\dl_")) {
         throw new ParserException(
               "Requires \\dl_ for introducing dynamic logic", text,
               keywordBegin);
      }
      // Get the following identifier without whitespaces
      final int identifierStart = keywordBegin + 4;
      final int identifierEnd = LexicalHelper.getIdentifier(text,
            identifierStart, end);

      // Parse the rest
      final ParseFunction rest = brackets(opt(new ExpressionParser(this.profile)
            .exprList()));

      final IASTNode dlcontent = rest.parse(text, identifierEnd, end);

      // Create the nodes
      final IASTNode keywordNode = Nodes.createKeyword(keywordBegin,
            identifierStart, keyword, "\\dl_");
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
