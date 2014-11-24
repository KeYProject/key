package de.key_project.jmlediting.profile.jmlref.keyword;

import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

public class AssignableKeyword implements ISpecificationStatementKeyword {

   @Override
   public String getKeyword() {
      return "assignable";
   }

   @Override
   public String getDescription() {
      return "An assignable clause gives a frame axiom for a specification. It says that, from the client's point of view, only the locations named, and locations in the data groups associated with these locations, can be assigned to during the execution of the method. The values of all subexpressions used in assignable clauses, such as i-1 in a[i-1], are computed in the pre-state of the method, because the assignable clause only talks about locations that exist in the pre-state.";
   }

}
