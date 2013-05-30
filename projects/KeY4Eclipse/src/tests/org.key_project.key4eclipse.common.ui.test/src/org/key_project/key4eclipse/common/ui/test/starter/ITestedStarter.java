package org.key_project.key4eclipse.common.ui.test.starter;

/**
 * Defines the common functionality to tes starter.
 * @author Martin Hentschel
 */
public interface ITestedStarter {
   /**
    * Returns The unique ID.
    * @return The unique ID.
    */
   public String getId();
   
   /**
    * Returns the name.
    * @return The name.
    */
   public String getName();
   
   /**
    * Returns the description.
    * @return The description.
    */
   public String getDescription();
}
