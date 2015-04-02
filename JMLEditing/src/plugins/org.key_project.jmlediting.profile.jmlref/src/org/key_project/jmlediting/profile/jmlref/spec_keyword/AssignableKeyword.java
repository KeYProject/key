package org.key_project.jmlediting.profile.jmlref.spec_keyword;

/**
 * The assignable keyword.
 *
 * @author Moritz Lichter
 *
 */
public class AssignableKeyword extends StoreRefContainerKeyword {

   /**
    * Creates a new assignable keyword instance.
    */
   public AssignableKeyword() {
      super("assignable", "assignable_redundantly", "modifiable",
            "modifiable_redundantly", "modifies", "modifies_redundantly");
   }

   @Override
   public String getDescription() {
      return "An assignable clause gives a frame axiom for a specification. "
            + "It says that, from the client's point of view, only the locations "
            + "named, and locations in the data groups associated with these "
            + "locations, can be assigned to during the execution of the method. "
            + "The values of all subexpressions used in assignable clauses, such "
            + "as i-1 in a[i-1], are computed in the pre-state of the method, "
            + "because the assignable clause only talks about locations that exist "
            + "in the pre-state.";
   }

   @Override
   boolean getProposeFinal() {
      return false;
   }

}
