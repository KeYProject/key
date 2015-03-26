package org.key_project.jmlediting.core.utilities;

/**
 * Enum for All JML ErrorTypes. All JML Errors that have to be Updated by
 * ErrorMarkerUpdater have to be listed here!
 *
 * @author David Giessing
 *
 */
public enum ErrorTypes {

   ParseError("org.key_project.jmlediting.core.parseerror"), ValidationError(
         "org.key_project.jmlediting.core.validationerror");

   private String id;

   private ErrorTypes(final String id) {
      this.id = id;
   }

   public String getId() {
      return this.id;
   }
}
