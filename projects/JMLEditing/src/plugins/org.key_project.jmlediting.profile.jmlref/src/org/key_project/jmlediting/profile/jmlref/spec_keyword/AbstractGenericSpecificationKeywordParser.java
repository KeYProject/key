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

      final IASTNode contentResult = this.parseToSemicolon(text, start + 1,
            closingSemicolon);
      return Nodes.createNode(contentResult.getStartOffset(),
            closingSemicolon + 1, NodeTypes.KEYWORD_CONTENT, contentResult);
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
      // By default most do not need them, if they, they should override
      // explicitly
   }

   protected abstract IASTNode parseToSemicolon(String text, int start, int end)
         throws ParserException;

}
