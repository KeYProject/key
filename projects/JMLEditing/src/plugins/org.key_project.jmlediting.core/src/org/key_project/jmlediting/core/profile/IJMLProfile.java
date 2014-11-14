package org.key_project.jmlediting.core.profile;

/**
 * Defines a profile for a JML variant.
 * 
 * @author Moritz Lichter
 *
 */
public interface IJMLProfile {

   /**
    * 
    * @return the name of the profile
    */
   String getName();

   /**
    * Returns a identifier for the profile which should be unique.
    * 
    * @return the identifier
    */
   String getIdentifier();

}
