package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.parser.ParserUtils;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AbstractGenericSpecificationKeywordParser;

public class StoreRefKeywordContentParser extends
AbstractGenericSpecificationKeywordParser {

   private StoreRefParser parser;

   @Override
   public void setProfile(final IJMLProfile profile) {
      this.parser = new StoreRefParser(profile);
   }

   @Override
   protected IASTNode parseToSemicolon(final String text, final int start,
         final int end) throws ParserException {
      return ParserUtils.requireComplete(this.parser).parse(text, start, end);
   }

}
