package de.key_project.jmlediting.profile.jmlref.keyword;

import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

public class EnsuresKeyword implements ISpecificationStatementKeyword {

   @Override
   public String getKeyword() {
      return "ensures";
   }

   @Override
   public String getDescription() {
      return "An ensures clause specifies a normal postcondition, i.e., a property that is guaranteed to hold at the end of the method (or constructor) invocation in the case that this method (or constructor) invocation returns without throwing an exception.";
   }

}
