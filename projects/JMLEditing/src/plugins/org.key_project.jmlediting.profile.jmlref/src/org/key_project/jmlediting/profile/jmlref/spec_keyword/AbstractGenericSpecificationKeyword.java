package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.profile.syntax.AbstractToplevelKeyword;

/**
 * Superclass for method specification keywords (called generic specification
 * clauses in the reference manual).
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractGenericSpecificationKeyword extends
      AbstractToplevelKeyword {

   /**
    * Creates a new keyword.
    *
    * @param keyword
    *           the keyword
    * @param keywords
    *           optional other keywords.
    */
   public AbstractGenericSpecificationKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

}
