package org.key_project.key4eclipse.resources.io;

/**
 * Exception for invalid metaFiles.
 * @author Stefan Käsdorf
 */
@SuppressWarnings("serial")
public class UnknownProofReferenceException extends Exception{
   
   /**
    * The Constructor
    */
   public UnknownProofReferenceException(String message){
      super(message);
   }
}
