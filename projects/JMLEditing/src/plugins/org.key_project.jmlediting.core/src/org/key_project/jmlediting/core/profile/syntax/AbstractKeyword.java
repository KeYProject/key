package org.key_project.jmlediting.core.profile.syntax;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * An {@link AbstractKeyword} does some default implementation for an
 * {@link IKeyword}.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractKeyword implements IKeyword {

   /**
    * A set of all supported keywords.
    */
   private final Set<String> keywords;

   /**
    * Creates a new {@link AbstractKeyword}. The list of supported keywords is
    * converted to a set, but for easier code the varargs are used in the
    * constructor,
    *
    * @param keywords
    *           all supported keywords
    */
   public AbstractKeyword(final String... keywords) {
      super();
      switch (keywords.length) {
      case 0:
         throw new IllegalArgumentException("Define at least one keyword");
      case 1:
         // Do some performance optimizations for the regular case that we have
         // only one keyword
         this.keywords = Collections.singleton(keywords[0]);
         break;
      default:
         this.keywords = Collections.unmodifiableSet(new HashSet<String>(Arrays
               .asList(keywords)));
      }
   }

   @Override
   public Set<String> getKeywords() {
      return this.keywords;
   }

}
