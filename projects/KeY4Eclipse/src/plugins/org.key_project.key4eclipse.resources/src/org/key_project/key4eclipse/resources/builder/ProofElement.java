package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.IMethod;

import de.uka.ilkd.key.proof.init.ProofOblInput;

public class ProofElement {
   
   private ProofOblInput proofObl;
   
   private IMethod method;
   
   private IFile proofFile;
   
   private IFile javaFile;
   
   public boolean hasProof;
   
   
   public ProofOblInput getProofObl() {
      return proofObl;
   }


   public IMethod getMethod() {
      return method;
   }
   
   public IFile getProofFile() {
      return proofFile;
   }


   public IFile getJavaFile() {
      return javaFile;
   }


   public ProofElement(ProofOblInput proofObl, IMethod method, IFile proofFile, IFile javaFile){
      this.proofObl = proofObl;
      this.method = method;
      this.proofFile = proofFile;
      this.javaFile = javaFile;
      if(proofFile == null){
         hasProof = false;
      }
      else{
         hasProof = true;
      }
   }
   
}
