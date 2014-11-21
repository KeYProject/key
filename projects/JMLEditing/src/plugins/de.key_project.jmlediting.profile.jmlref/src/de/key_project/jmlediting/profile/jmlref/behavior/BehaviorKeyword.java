package de.key_project.jmlediting.profile.jmlref.behavior;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorKeyword;

public class BehaviorKeyword implements IJMLBehaviorKeyword {

   private static final Set<String> KEYWORDS = Collections.unmodifiableSet(new HashSet<String>(Arrays.asList("behavior", "behaviour")));
   
   @Override
   public Set<String> getKeywords() {
      return KEYWORDS;
   }

}
