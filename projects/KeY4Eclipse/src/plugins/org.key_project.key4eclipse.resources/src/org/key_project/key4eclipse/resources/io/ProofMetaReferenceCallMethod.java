package org.key_project.key4eclipse.resources.io;

import java.util.List;

public class ProofMetaReferenceCallMethod extends ProofMetaReferenceMethod {

   private List<ProofMetaReferenceMethod> subImpl;
   
   public ProofMetaReferenceCallMethod(String kjt, String name,
         String parameters, String source,
         List<ProofMetaReferenceMethod> subImpl) {
      super(kjt, name, parameters, source);
      this.subImpl = subImpl;
   }

   public List<ProofMetaReferenceMethod> getSubImpl() {
      return subImpl;
   }

   public void addSubMethod(ProofMetaReferenceMethod subMethod) {
      subImpl.add(subMethod);
   }
      
}
