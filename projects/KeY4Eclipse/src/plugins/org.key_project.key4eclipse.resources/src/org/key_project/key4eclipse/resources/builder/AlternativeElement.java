package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.resources.IFile;

import de.uka.ilkd.key.proof.init.ProofOblInput;

public class AlternativeElement {
   private ProofOblInput proofObl;
   private IFile javaFile;
   private int lineNumber;
   public ProofOblInput getProofObl() {
      return proofObl;
   }
   public IFile getJavaFile() {
      return javaFile;
   }
   public int getLineNumber() {
      return lineNumber;
   }
   
   public AlternativeElement(ProofOblInput obl, IFile javaFile, int lineNumber){
      this.proofObl = obl;
      this.javaFile = javaFile;
      this.lineNumber = lineNumber;
   }
}
