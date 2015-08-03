package org.key_project.key4eclipse.resources.io;

/**
 * Represents a call method reference for the ProofMetaReferences
 * @author Stefan Käsdorf
 */
public class ProofMetaReferenceCallMethod {

   private String kjt;
   private String name;
   private String parameters; 
   private String implementations;
   
   public ProofMetaReferenceCallMethod(String kjt, String name,
         String parameters, String implementations) {
      this.kjt = kjt;
      this.name = name;
      this.parameters = parameters;
      this.implementations = implementations;
   }

   public String getKjt() {
      return kjt;
   }

   public String getName() {
      return name;
   }

   public String getParameters() {
      return parameters;
   }

   public String getImplementations() {
      return implementations;
   }
      
}
