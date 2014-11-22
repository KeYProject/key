package de.key_project.jmlediting.profile.jmlref.keyword;

import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

public class RequiresKeyword implements ISpecificationStatementKeyword {

   @Override
   public String getKeyword() {
      return "requires";
   }

   @Override
   public String getDescription() {
      return "A requires clause specifies a precondition of method or constructor.";
   }

}
