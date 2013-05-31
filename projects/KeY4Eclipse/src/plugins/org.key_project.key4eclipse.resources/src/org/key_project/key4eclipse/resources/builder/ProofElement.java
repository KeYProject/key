package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.resources.IFile;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.init.ProofOblInput;

public class ProofElement {
   private ProofOblInput proofObl;
   private IFile javaFile;
   private SourceLocation scl;
   private KeYJavaType kjt;
   
   public ProofOblInput getProofObl() {
      return proofObl;
   }
   public IFile getJavaFile() {
      return javaFile;
   }
   public SourceLocation getSourceLocation() {
      return scl;
   }
   
   public KeYJavaType getKeYJavaType(){
      return kjt;
   }
   
   public ProofElement(ProofOblInput obl, IFile javaFile, SourceLocation scl, KeYJavaType kjt){
      this.proofObl = obl;
      this.javaFile = javaFile;
      this.scl = scl;
      this.kjt = kjt;
   }
}
