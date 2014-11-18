package org.key_project.jmlediting.core.profile.syntax;

import java.util.Set;

public interface IJMLBehaviorSpecification {

   /**
    * Returns the set of keywords which introduces the specification. A set
    * instead of a single string is used because the JML Reference allows for
    * example "behavior" and "behaviour" as keyword for the same clause. The set
    * has to be non empty.
    * 
    * @return a set of strings containing the introducing keywords
    */
   Set<String> getKeywords();

}
