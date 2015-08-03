package org.key_project.key4eclipse.resources.io;

/**
 * Represents a inline method reference for the ProofMetaReferences
 * @author Stefan Käsdorf
 */
public class ProofMetaReferenceMethod {

   private String kjt;
   private String name;
   private String parameters;
   private String source;
   
   public ProofMetaReferenceMethod(String kjt, String name,
         String parameters, String source) {
      this.kjt = kjt;
      this.name = name;
      this.parameters = parameters;
      this.source = source;
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

   public String getSource() {
      return source;
   }
      
}
