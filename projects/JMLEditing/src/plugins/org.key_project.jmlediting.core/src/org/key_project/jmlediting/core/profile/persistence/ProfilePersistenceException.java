package org.key_project.jmlediting.core.profile.persistence;

/**
 * An exception which signals that the persistence of a profile failed.
 *
 * @author Moritz Lichter
 *
 */
public class ProfilePersistenceException extends Exception {

   /**
    *
    */
   private static final long serialVersionUID = 410693400936068797L;

   public ProfilePersistenceException() {
      super();
   }

   public ProfilePersistenceException(final String arg0, final Throwable arg1) {
      super(arg0, arg1);
   }

   public ProfilePersistenceException(final String message) {
      super(message);
   }

   public ProfilePersistenceException(final Throwable cause) {
      super(cause);
   }

}
