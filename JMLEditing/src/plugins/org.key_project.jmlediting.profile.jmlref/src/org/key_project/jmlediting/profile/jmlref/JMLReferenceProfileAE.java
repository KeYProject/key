package org.key_project.jmlediting.profile.jmlref;

/**
 * The JML reference profile for American English keywords.
 *
 * @author Moritz Lichter
 *
 */
public class JMLReferenceProfileAE extends JMLReferenceProfile {

   /**
    * Creates a new profile instance.
    */
   public JMLReferenceProfileAE() {
      super(KeywordLocale.AMERICAN);
   }

   @Override
   public String getName() {
      return "JML Reference (American)";
   }

   @Override
   public String getIdentifier() {
      return "org.key_project.jmlediting.profile.jmlref.ae";
   }

}
