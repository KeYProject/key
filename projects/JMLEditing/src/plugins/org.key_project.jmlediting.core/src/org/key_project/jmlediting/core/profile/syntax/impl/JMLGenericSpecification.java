package org.key_project.jmlediting.core.profile.syntax.impl;

import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;

public class JMLGenericSpecification implements IJMLGenericSpecification {
   
   private final String keyword;
   
   public JMLGenericSpecification(final String keyword) {
      if (keyword == null || keyword.length() == 0) {
         throw new IllegalArgumentException("Illegal keyword. Not allowed to be null or empty");
      }
      this.keyword = keyword;
   }

   @Override
   public String getKeyword() {
      return this.keyword;
   }

}
