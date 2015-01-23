package org.key_project.jmlediting.profile.jmlref.quantifier;

public class ForallQuantifierKeyword extends AbstractQuantifierKeyword {

   public ForallQuantifierKeyword() {
      super("\\forall");
   }

   @Override
   public String getDescription() {
      return "The quantifier \\forall is the universal quantifier.";
   }

}
