package org.key_project.jmlediting.profile.jmlref.quantifier;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

/**
 * The abstract implementation for the {@link IQuantifierKeyword} which does not
 * contains a keyword specific content. The content of the quantifier is parsed
 * by {@link QuantifierPrimary}.
 * 
 * @author Moritz Lichter
 *
 */
public abstract class AbstractQuantifierKeyword extends AbstractEmptyKeyword
      implements IQuantifierKeyword {

   /**
    * Creates a new {@link AbstractQuantifierKeyword} with the given keyword.
    * 
    * @param keyword
    *           the keyword of the quantifier
    */
   public AbstractQuantifierKeyword(final String keyword) {
      super(keyword);
   }

}
