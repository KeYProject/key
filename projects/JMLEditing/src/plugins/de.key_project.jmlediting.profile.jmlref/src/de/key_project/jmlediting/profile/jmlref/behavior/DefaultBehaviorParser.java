package de.key_project.jmlediting.profile.jmlref.behavior;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

public class DefaultBehaviorParser implements IKeywordParser {

   @Override
   public IASTNode parse(String text, int start, int end)
         throws ParserException {
      // We do not parse anything for a behavior because we expect other keywords in the follow
      return null;
   }

}
