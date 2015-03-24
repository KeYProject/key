package org.key_project.jmlediting.profile.jmlref.behavior;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.EmptyKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordAutoProposer;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.IKeywordValidator;
import org.key_project.jmlediting.core.profile.syntax.ToplevelKeywordSort;
import org.key_project.jmlediting.profile.jmlref.KeywordLocale;

/**
 * Base class for all behavior keywords. It allows to specify two keywords for
 * American and for British English and to choose which one to use.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractBehaviorKeyword implements IKeyword {

   /**
    * The keywords, which are available.
    */
   private Set<String> keywords;

   /**
    * Creates a keyword for an behavior.
    *
    * @param locale
    *           the locale for the keywords
    * @param americanEnglishKeyword
    *           the AE keyword
    * @param britishEnglishKeyword
    *           the BE keyword
    */
   public AbstractBehaviorKeyword(final KeywordLocale locale,
         final String americanEnglishKeyword, final String britishEnglishKeyword) {
      switch (locale) {
      case AMERICAN:
         this.keywords = Collections.singleton(americanEnglishKeyword);
         break;
      case BRITISH:
         this.keywords = Collections.singleton(britishEnglishKeyword);
         break;
      case BOTH:
         this.keywords = Collections.unmodifiableSet(new HashSet<String>(Arrays
               .asList(americanEnglishKeyword, britishEnglishKeyword)));
         break;
      default:
         throw new AssertionError("Illegal case statment");
      }
   }

   @Override
   public Set<String> getKeywords() {
      return this.keywords;
   }

   @Override
   public IKeywordParser createParser() {
      return EmptyKeywordParser.getInstance();
   }

   @Override
   public IKeywordAutoProposer createAutoProposer() {
      return null;
   }

   @Override
   public IKeywordSort getSort() {
      return ToplevelKeywordSort.INSTANCE;
   }

   @Override
   public IKeywordValidator getKeywordValidator() {
      return null;
   }

}