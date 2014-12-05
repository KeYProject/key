package org.key_project.jmlediting.core.profile.syntax;

public abstract class AbstractEmptyKeyword extends AbstractKeyword {

   public AbstractEmptyKeyword(final String keyword, final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordParser createParser() {
      return EmptyKeywordParser.getInstance();
   }

}
