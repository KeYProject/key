package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.MeasuredByKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;

/**
 * The key measured by keywords, which supports another content type than the
 * JML reference version.
 * 
 * @author Moritz Lichter
 *
 */
public class KeYMeasuredByKeyword extends MeasuredByKeyword {

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            return new SpecExpressionParser(profile).exprList();
         }
      };
   }

}
