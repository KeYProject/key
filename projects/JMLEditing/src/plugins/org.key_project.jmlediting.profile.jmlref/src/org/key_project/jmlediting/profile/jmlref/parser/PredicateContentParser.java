package org.key_project.jmlediting.profile.jmlref.parser;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;

public class PredicateContentParser extends SemicolonClosedKeywordParser {

   @Override
   protected ParseFunction createContentParseFunction(final IJMLProfile profile) {
      return new PredicateParser(profile);
   }

}
