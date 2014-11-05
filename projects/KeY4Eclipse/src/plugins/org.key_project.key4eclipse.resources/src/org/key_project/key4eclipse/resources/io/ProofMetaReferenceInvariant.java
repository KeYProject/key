package org.key_project.key4eclipse.resources.io;

public class ProofMetaReferenceInvariant {
   
   private String kjt;
   private String name;
   private String originalInv;
   
   public ProofMetaReferenceInvariant(String kjt, String name, String originalInv) {
      this.kjt = kjt;
      this.name = name;
      this.originalInv = originalInv;
   }

   public String getKjt() {
      return kjt;
   }

   public String getName() {
      return name;
   }

   public String getOriginalInv() {
      return originalInv;
   }
   
}
