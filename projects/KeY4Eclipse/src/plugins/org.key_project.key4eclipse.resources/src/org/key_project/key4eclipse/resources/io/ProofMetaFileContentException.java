package org.key_project.key4eclipse.resources.io;

/**
 * Exception for invalid metaFiles.
 * @author Stefan Käsdorf
 */
@SuppressWarnings("serial")
public class ProofMetaFileContentException extends Exception{
   
   /**
    * The Constructor
    */
   public ProofMetaFileContentException(String message){
      super(message);
   }
}
