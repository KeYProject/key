package org.key_project.key4eclipse.resources.io;

public class ProofMetaReferenceAccess {

   private String kjt;
   private String name;
   private String source;
   
   public ProofMetaReferenceAccess(String kjt, String name, String source){
      this.kjt = kjt;
      this.name = name;
      this.source = source;
   }

   public String getKjt() {
      return kjt;
   }

   public String getName() {
      return name;
   }

   public String getSource() {
      return source;
   }
   
}
