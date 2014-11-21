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

   @Override
   public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result
            + ((description == null) ? 0 : description.hashCode());
      result = prime * result + ((keyword == null) ? 0 : keyword.hashCode());
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
      JMLGenericSpecification other = (JMLGenericSpecification) obj;
      if (description == null) {
         if (other.description != null)
            return false;
      }
      else if (!description.equals(other.description))
         return false;
      if (keyword == null) {
         if (other.keyword != null)
            return false;
      }
      else if (!keyword.equals(other.keyword))
         return false;
      return true;
   }

   
   
}
