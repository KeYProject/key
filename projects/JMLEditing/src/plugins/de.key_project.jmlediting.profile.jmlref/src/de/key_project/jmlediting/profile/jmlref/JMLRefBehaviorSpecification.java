package de.key_project.jmlediting.profile.jmlref;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;

public class JMLRefBehaviorSpecification implements IJMLBehaviorSpecification{

   private static final Set<String> BEHAVIOR_KEYWORDS;
   
   static {
      BEHAVIOR_KEYWORDS = Collections.unmodifiableSet(new HashSet<String>(Arrays.asList("behavior", "behaviour")));
   }
   
   @Override
   public Set<String> getKeywords() {
      return BEHAVIOR_KEYWORDS;
   }

}
