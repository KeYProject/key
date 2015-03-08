package org.key_project.jmlediting.profile.jmlref.visibility;

/**
 * The spec_public keyword.
 *
 * @author Moritz Lichter
 *
 */
public class SpecPublicKeyword extends JMLModifierKeyword {

   /**
    * Creates a new instance for the spec_public keyword.
    */
   public SpecPublicKeyword() {
      super("spec_public");
   }

   @Override
   public String getDescription() {
      return "The spec_public modifier allows one to declare a feature as public "
            + "for specification purposes. It can only be used when the feature "
            + "has a more restrictive visibility in Java. A spec_public field is "
            + "also implicitly a data group.";
   }
}
