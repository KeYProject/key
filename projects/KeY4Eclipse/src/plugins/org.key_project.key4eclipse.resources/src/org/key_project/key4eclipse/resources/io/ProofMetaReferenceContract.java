package org.key_project.key4eclipse.resources.io;

/**
 * Represents a contract reference for the ProofMetaReferences
 * @author Stefan Käsdorf
 */
public class ProofMetaReferenceContract {
   
   private String name;
   private String contract;
   
   public ProofMetaReferenceContract(String name, String contract) {
      this.name = name;
      this.contract = contract;
   }

   public String getName() {
      return name;
   }

   public String getContract() {
      return contract;
   }
   
}
