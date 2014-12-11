package org.key_project.jmlediting.profile.jmlref.spec_keyword;


public class AccessibleKeyword extends StoreRefKeyword {
   public AccessibleKeyword() {
      super("accessible");
   }

   @Override
   public String getDescription() {
      return "During execution of the method (which includes all directly and indirectly called methods and constructors), only locations that either did not exist in the pre-state, that are local to the method (including the method's formal parameters), or that are either named in the lists found in the accessible and assignable clauses or that are dependees of such locations, are read from.";
   }

}
