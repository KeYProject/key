package org.key_project.jmlediting.profile.jmlref.visibility;

/**
 * The spec_protected keyword.
 *
 * @author Moritz Lichter
 *
 */
public class SpecProtectedKeyword extends JMLModifierKeyword {

   /**
    * Creates a new spec_protected keyword.
    */
   public SpecProtectedKeyword() {
      super("spec_protected");
   }

   @Override
   public String getDescription() {
      return "The spec_protected modifier allows one to declare a feature as "
            + "protected for specification purposes. It can only be used when "
            + "the feature has a more restrictive visibility in Java. That is, "
            + "it can only be used to change the visibility of a field or method "
            + "that is, for Java, either declared private or default access "
            + "(package visible). A spec_protected field is also implicitly a data group.";
   }

}
