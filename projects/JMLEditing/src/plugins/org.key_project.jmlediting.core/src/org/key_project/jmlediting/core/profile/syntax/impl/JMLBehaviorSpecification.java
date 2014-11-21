package org.key_project.jmlediting.core.profile.syntax.impl;

import java.util.Collections;
import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;

public class JMLBehaviorSpecification implements IJMLBehaviorSpecification {

   private final Set<String> keywords;

   public JMLBehaviorSpecification(Set<String> keywords) {
      super();
      this.keywords = keywords;
   }

   @Override
   public Set<String> getKeywords() {
      return Collections.unmodifiableSet(this.keywords);
   }

   @Override
   public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + ((keywords == null) ? 0 : keywords.hashCode());
      return result;
   }

   @Override
   public boolean equals(Object obj) {
      if (this == obj)
         return true;
      if (obj == null)
         return false;
      if (getClass() != obj.getClass())
         return false;
      JMLBehaviorSpecification other = (JMLBehaviorSpecification) obj;
      if (keywords == null) {
         if (other.keywords != null)
            return false;
      }
      else if (!keywords.equals(other.keywords))
         return false;
      return true;
   }
   
   

}
