package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.LexicalHelper;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IJMLPrimary;

public class DynamicLogicPrimary implements IJMLPrimary {

   private static class DL_Keyword extends AbstractEmptyKeyword {

      public DL_Keyword() {
         super("\\dl_");
      }

      @Override
      public String getDescription() {
         return null;
      }

   }

   private static DL_Keyword keyword = new DL_Keyword();

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      final int keywordBegin = LexicalHelper.skipWhiteSpacesOrAt(text, start,
            end);
      if (end - keywordBegin < 4
            || !text.subSequence(keywordBegin, keywordBegin + 4)
                  .equals("\\dl_")) {
         throw new ParserException(
               "Requires \\dl_ for introducing dynamic logic", text,
               keywordBegin);
      }
      final int identifierStart = keywordBegin + 4;
      final int identifierEnd = LexicalHelper.getIdentifier(text,
            identifierStart, end);
      final int whiteSpaceEnd = LexicalHelper.skipWhiteSpacesOrAt(text,
            identifierEnd, end);
      if (text.charAt(whiteSpaceEnd) != '(') {
         throw new ParserException("Expected open pharentesis", text,
               whiteSpaceEnd);
      }
      final int contentStart = LexicalHelper.skipWhiteSpacesOrAt(text,
            whiteSpaceEnd + 1, end);
      final int contentEnd = LexicalHelper.scanForClosingCharacter(')', text,
            contentStart, end);

      final IASTNode keywordNode = Nodes.createKeyword(keywordBegin,
            identifierStart, keyword, "\\dl_");
      final IASTNode identifier = Nodes.createString(identifierStart,
            identifierEnd, text.substring(identifierStart, identifierEnd));
      final IASTNode stringContent = Nodes.createString(contentStart,
            contentEnd, text.substring(contentStart, contentEnd));
      final IASTNode content = Nodes.createNode(identifierStart,
            contentEnd + 1, NodeTypes.KEYWORD_CONTENT, identifier,
            stringContent);
      final IASTNode keywordAppl = Nodes.createNode(NodeTypes.KEYWORD_APPL,
            keywordNode, content);
      return keywordAppl;
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
   }

}
