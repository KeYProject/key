package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AssignableKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.key.locset.LocSetExprListParser;

public class KeyAssignableKeyword extends AssignableKeyword {

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLProfile profile) {
            return new LocSetExprListParser(profile);
         }
      };
   }
}
