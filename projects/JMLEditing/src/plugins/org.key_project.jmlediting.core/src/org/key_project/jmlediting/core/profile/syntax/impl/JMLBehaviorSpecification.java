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

}
