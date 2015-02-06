package org.key_project.jmlediting.profile.jmlref.spec_keyword;

/**
 * The accessible keyword.
 *
 * @author Moritz Lichter
 *
 */
public class AccessibleKeyword extends StoreRefContainerKeyword {

   /**
    * Creates a new instance for the accessible keyword.
    */
   public AccessibleKeyword() {
      super("accessible");
   }

   @Override
   public String getDescription() {
      return "During execution of the method (which includes all directly and "
            + "indirectly called methods and constructors), only locations that "
            + "either did not exist in the pre-state, that are local to the "
            + "method (including the method's formal parameters), or that are "
            + "either named in the lists found in the accessible and assignable "
            + "clauses or that are dependees of such locations, are read from.";
   }

   @Override
   boolean getProposeFinal() {
      return true;
   }

}
