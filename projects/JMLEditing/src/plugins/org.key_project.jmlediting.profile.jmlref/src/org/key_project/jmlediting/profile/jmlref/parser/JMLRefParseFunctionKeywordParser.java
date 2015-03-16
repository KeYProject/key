package org.key_project.jmlediting.profile.jmlref.parser;

import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;

public abstract class JMLRefParseFunctionKeywordParser extends
      ParseFunctionKeywordParser<IJMLExpressionProfile> {

   public JMLRefParseFunctionKeywordParser() {
      super(IJMLExpressionProfile.class);
   }

}
