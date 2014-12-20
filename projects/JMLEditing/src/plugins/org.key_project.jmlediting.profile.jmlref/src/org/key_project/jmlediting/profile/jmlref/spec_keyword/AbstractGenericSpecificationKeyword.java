package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;

public abstract class AbstractGenericSpecificationKeyword extends
      AbstractKeyword implements IToplevelKeyword {

   public AbstractGenericSpecificationKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

}
