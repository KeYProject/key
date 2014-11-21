package org.key_project.jmlediting.core.profile.syntax.impl;

import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;

public class JMLGenericSpecification implements IJMLGenericSpecification {
   
   private final String keyword;
   private final String description;
   
   public JMLGenericSpecification(final String keyword, final String description) {
      if (keyword == null || keyword.length() == 0) {
         throw new IllegalArgumentException("Illegal keyword. Not allowed to be null or empty");
      }
      if (description == null) {
         throw new IllegalArgumentException("Cannot pass a null description");
      }
      this.keyword = keyword;
      this.description = description;
   }

   @Override
   public String getKeyword() {
      return this.keyword;
   }

   @Override
   public String getDescription() {
      return this.description;
   }

}
