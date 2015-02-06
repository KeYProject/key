package org.key_project.jmlediting.profile.key.other;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AccessibleKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.ParseFunctionGenericKeywordParser;
import org.key_project.jmlediting.profile.key.locset.LocSetExprListParser;

public class KeyAccessibleKeyword extends AccessibleKeyword {

   public KeyAccessibleKeyword() {

   }

   @Override
   public IKeywordParser createParser() {
      return new ParseFunctionGenericKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLProfile profile) {
            final LocSetExprListParser locSetExprList = new LocSetExprListParser(
                  profile);
            return alt(
                  seq(alt(ident(), keywords(InvKeyword.class, profile)),
                        constant(":"), locSetExprList), locSetExprList);
         }

      };
   }

}
