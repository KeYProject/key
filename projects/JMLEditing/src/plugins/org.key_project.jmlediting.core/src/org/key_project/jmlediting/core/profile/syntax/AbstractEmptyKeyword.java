package org.key_project.jmlediting.core.profile.syntax;

/**
 * Implements a keyword which does not require any content after the keyword.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractEmptyKeyword extends AbstractKeyword {

   /**
    * Creates a new empty keyword with the given supported strings.
    * 
    * @param keyword
    *           the first keyword
    * @param keywords
    *           all other supported keywords
    */
   public AbstractEmptyKeyword(final String keyword, final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordParser createParser() {
      return EmptyKeywordParser.getInstance();
   }

}
