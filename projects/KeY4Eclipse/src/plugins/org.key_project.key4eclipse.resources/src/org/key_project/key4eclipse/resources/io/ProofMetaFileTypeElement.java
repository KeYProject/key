package org.key_project.key4eclipse.resources.io;

import java.util.LinkedList;

/**
 * An Object that provides the content of a meta files type.
 * @author Stefan Käsdorf
 */
public class ProofMetaFileTypeElement {
//TODO remove this class an extend the reader.
   private String type;
   private LinkedList<String> subTypes;
   
   public ProofMetaFileTypeElement(String type, LinkedList<String> subTypes){
      this.type = type;
      this.subTypes = subTypes;
   }

   public String getType() {
      return type;
   }

   public LinkedList<String> getSubTypes() {
      return subTypes;
   }
   
}
