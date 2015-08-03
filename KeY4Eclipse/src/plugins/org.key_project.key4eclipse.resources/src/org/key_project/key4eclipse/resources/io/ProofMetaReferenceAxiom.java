package org.key_project.key4eclipse.resources.io;

/**
 * Represents an axiom reference for the ProofMetaReferences
 * @author Stefan Käsdorf
 */
public class ProofMetaReferenceAxiom {

   private String kjt;
   private String name;
   private String originalRep;
   
   public ProofMetaReferenceAxiom(String kjt, String name, String originalRep) {
      this.kjt = kjt;
      this.name = name;
      this.originalRep = originalRep;
   }

   public String getKjt() {
      return kjt;
   }

   public String getName() {
      return name;
   }

   public String getOriginalRep() {
      return originalRep;
   }
   
}
