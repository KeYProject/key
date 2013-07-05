package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedHashSet;

public class RecursionGraphNode {

   private ProofElement element;
   private LinkedHashSet<RecursionGraphNode> preds;
   private LinkedHashSet<RecursionGraphNode> succs;
   private LinkedHashSet<ProofElement> succElements;
   
   public RecursionGraphNode(ProofElement pe, LinkedHashSet<ProofElement> succElements){
      element = pe;
      preds = new LinkedHashSet<RecursionGraphNode>();
      succs = new LinkedHashSet<RecursionGraphNode>();
      this.succElements = succElements;
   }
   
   public ProofElement getProofElement(){
      return element;
   }
   
   public LinkedHashSet<ProofElement> getSuccElements(){
      return succElements;
   }

   public void addPred(RecursionGraphNode pred){
      preds.add(pred);
   }
   
   public void addSucc(RecursionGraphNode succ){
      succs.add(succ);
   }
   
   public boolean hasSucc(){
      return !succs.isEmpty();
   }
   
   public boolean hasPred(){
      return !preds.isEmpty();
   }
   
   public LinkedHashSet<RecursionGraphNode> getSuccs(){
      return succs;
   }
   
   public LinkedHashSet<RecursionGraphNode> getPreds(){
      return preds;
   }
}
