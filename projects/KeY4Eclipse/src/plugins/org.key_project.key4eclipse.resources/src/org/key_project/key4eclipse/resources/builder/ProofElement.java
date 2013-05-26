package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.IMethod;

import de.uka.ilkd.key.proof.init.ProofOblInput;

public class ProofElement {
   
   private ProofOblInput proofObl;
   
   private IMethod method;
   
   private IFile proofFile;
   
   private IFile javaFile;
   
   private LinkedList<String> types;   
   
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
   
   public LinkedList<String> getTypes(){
      return types;
   }


   public ProofElement(ProofOblInput proofObl, IMethod method, IFile proofFile, IFile javaFile, LinkedList<String> types){
      this.proofObl = proofObl;
      this.method = method;
      this.proofFile = proofFile;
      this.javaFile = javaFile;
      this.types = types;
   }
   
   public boolean hasProof(){
      if(proofFile == null){
         return false;
      }
      else {
         return true;
      }
   }
   
}
