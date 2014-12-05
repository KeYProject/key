package de.key_project.jmlediting.profile.jmlref.spec_keyword;

import static org.key_project.jmlediting.core.parser.LexicalHelper.scanForClosingSemicolon;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

public abstract class AbstractGenericSpecificationKeywordParser implements
      IKeywordParser {

   @Override
   public IASTNode parse(String text, int start, int end)
         throws ParserException {
      int closingSemicolon = scanForClosingSemicolon(text, start, end);
      

      return this.parseToSemicolon(text, start+1, closingSemicolon);
   }
   
   protected abstract IASTNode parseToSemicolon(String text, int start, int end);

}
