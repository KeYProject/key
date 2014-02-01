package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedHashSet;

public class RecNode {

   private ProofElement pe;
   private LinkedHashSet<ProofElement> succElements;
   
   public RecNode(ProofElement pe, LinkedHashSet<ProofElement> succElements){
      this.pe = pe;
      this.succElements = succElements;
   }
}
