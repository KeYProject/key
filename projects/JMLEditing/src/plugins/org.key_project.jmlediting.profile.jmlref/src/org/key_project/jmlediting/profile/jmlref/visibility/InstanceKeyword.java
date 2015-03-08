package org.key_project.jmlediting.profile.jmlref.visibility;

/**
 * Implementation of the instance modifier.
 * 
 * @author Moritz Lichter
 *
 */
public class InstanceKeyword extends JMLModifierKeyword {

   /**
    * Creayes a new keyword instance.
    */
   public InstanceKeyword() {
      super("instance");
   }

   @Override
   public String getDescription() {
      return "The instance modifier says that a field is not static.";
   }

}
