package org.key_project.jmlediting.profile.jmlref.usercontent;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.user.AbstractUserDefinedKeywordContentDescription;
import org.key_project.jmlediting.profile.jmlref.Activator;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;

public class SpecExpressionContentDescription extends
      AbstractUserDefinedKeywordContentDescription {

   @Override
   public String getId() {
      return Activator.PLUGIN_ID + ".spec_expression";
   }

   @Override
   public String getDescription() {
      return "JML Expression";
   }

   @Override
   public ClosingCharacterLaw getClosingCharacterLaw() {
      return ClosingCharacterLaw.ALLOWED;
   }

   @Override
   protected ParseFunction getContentParseFunction(final IJMLProfile profile) {
      return new SpecExpressionParser(profile);
   }

}
