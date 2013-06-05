package org.key_project.key4eclipse.resources.io;

import java.util.LinkedList;

public class ProofMetaFileTypeElement {

   private String type;
   private boolean hasSubTypes;
   private LinkedList<String> subTypes;
   
   public ProofMetaFileTypeElement(String type, LinkedList<String> subTypes){
      this.type = type;
      this.subTypes = subTypes;
      this.hasSubTypes = !subTypes.isEmpty();
   }

   public String getType() {
      return type;
   }

   public boolean isHasSubTypes() {
      return hasSubTypes;
   }

   public LinkedList<String> getSubTypes() {
      return subTypes;
   }
   
}
