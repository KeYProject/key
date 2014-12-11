package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AbstractGenericSpecificationKeywordParser;

public class StoreRefKeywordContentParser extends
AbstractGenericSpecificationKeywordParser {

   private StoreRefParser parser;
   private final boolean allowInformalDescription;

   public StoreRefKeywordContentParser(final boolean allowInformalDescription) {
      super();
      this.allowInformalDescription = allowInformalDescription;
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
      this.parser = new StoreRefParser(profile, this.allowInformalDescription);
   }

   @Override
   protected IASTNode parseToSemicolon(final String text, final int start,
         final int end) throws ParserException {
      return ParserBuilder.requireComplete(this.parser).parse(text, start, end);
   }

}
