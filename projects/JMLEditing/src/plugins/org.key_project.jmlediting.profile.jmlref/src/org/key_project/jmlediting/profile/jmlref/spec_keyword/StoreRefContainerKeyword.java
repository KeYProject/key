package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.profile.syntax.IKeywordAutoProposer;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.StoreRefKeywordContentParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordProposer;

/**
 * A keyword, which contains storage references as content.
 *
 * @author Moritz Lichter
 *
 */
public abstract class StoreRefContainerKeyword extends
      AbstractGenericSpecificationKeyword {

   /**
    * Creates a new {@link StoreRefContainerKeyword}.
    *
    * @param keyword
    *           the keyword
    * @param keywords
    *           optional other keywords
    */
   public StoreRefContainerKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordParser createParser() {
      return JMLRefParseFunctionKeywordParser
            .semicolonClosed(new StoreRefKeywordContentParser(true));
   }

   @Override
   public IKeywordAutoProposer createAutoProposer() {
      return new StoreRefKeywordProposer(this.getProposeFinal());
   }

   /**
    * @return whether to propose final fields and parameters or not
    */
   abstract boolean getProposeFinal();

}
