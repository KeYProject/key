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

public class DefaultJMLParser implements IJMLParser {

   private IJMLProfile profile;

   public DefaultJMLParser(IJMLProfile profile) {
      if (profile == null) {
         throw new IllegalArgumentException("Cannot pass a null profile");
      }
      this.profile = profile;
   }
   
   @Override
   public IASTNode parse(String text, int start, int end) throws ParserException{
      List<IASTNode> allKeywords = new ArrayList<IASTNode> ();
      
      int position = skipWhiteSpacesOrAt(text, start, end);
      while (position < end) {
         IASTNode keywordNode = parseKeyword(text, position, end);
         allKeywords.add(keywordNode);
         position = skipWhiteSpacesOrAt(text, keywordNode.getEndOffset() +1, end);
      }
      
      if (allKeywords.size() == 0) {
         throw new ParserException("Nothing specified", text, start);
      }
      
      return Nodes.createNode(NodeTypes.NODE, allKeywords);
   }

   private IASTNode parseKeyword(String text, int start, int end)
         throws ParserException {
      validatePositions(text, start, end);
      int keywordStart = skipWhiteSpacesOrAt(text, start, end);
      int keywordEnd = getIdentifier(text, keywordStart, end);
      String keyword = text.substring(keywordStart, keywordEnd);
      IKeyword foundKeyword = null;
      for (IKeyword availableKeyword : this.profile.getSupportedKeywords()) {
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
      IASTNode keywordNode = Nodes.createKeyword(keywordStart, keywordEnd, foundKeyword, keyword);
      
      // Now parse according to the keywword
      IKeywordParser keywordParser = foundKeyword.createParser();
      IASTNode keywordResult = keywordParser.parse(text, keywordEnd, end);
      
      if (keywordResult == null) {
         return keywordNode;
      } else {
         return Nodes.createNode(NodeTypes.KEYWORD_APPL, keywordNode, keywordResult);
      }
   }

}
