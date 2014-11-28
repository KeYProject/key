package org.key_project.jmlediting.core.profile.syntax;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public abstract class AbstractKeyword implements IKeyword {

   private final Set<String> keywords;

   public AbstractKeyword(String... keywords) {
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
