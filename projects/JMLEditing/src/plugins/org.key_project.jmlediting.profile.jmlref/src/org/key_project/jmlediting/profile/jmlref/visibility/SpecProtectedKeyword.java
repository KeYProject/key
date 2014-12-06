package org.key_project.jmlediting.profile.jmlref.visibility;

public class SpecProtectedKeyword extends JMLVisibilityKeyword {

   public SpecProtectedKeyword() {
      super("spec_protected");
   }

   @Override
   public String getDescription() {
      return "The spec_protected modifier allows one to declare a feature as protected for specification purposes. It can only be used when the feature has a more restrictive visibility in Java. That is, it can only be used to change the visibility of a field or method that is, for Java, either declared private or default access (package visible). A spec_protected field is also implicitly a data group.";
   }

}
