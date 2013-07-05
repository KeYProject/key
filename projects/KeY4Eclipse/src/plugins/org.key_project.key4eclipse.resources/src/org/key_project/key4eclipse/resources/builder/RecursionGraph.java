package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedHashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.Contract;


public class RecursionGraph {
   
   private LinkedHashSet<RecursionGraphNode> nodes;
   private LinkedList<ProofElement> proofElements;
   private LinkedHashSet<RecursionGraphNode> cyclingNodes;

   
   public RecursionGraph(LinkedList<ProofElement> proofElements){
      nodes = new LinkedHashSet<RecursionGraphNode>();
      this.proofElements = proofElements;
      for(ProofElement pe : this.proofElements){
         addProofElement(pe);
      }
   }
   
   
   public void addProofElement(ProofElement pe){
      RecursionGraphNode node = new RecursionGraphNode(pe, getSuccElements(pe, proofElements));
      addNode(node);
   }
   
   
   public void addNode(RecursionGraphNode node){
      updatePreds(node);
      updateSuccs(node);
      nodes.add(node);
   }
   
   private void updateSuccs(RecursionGraphNode node){
      for(RecursionGraphNode succNode : nodes){
         if(node.getSuccElements().contains(succNode.getProofElement())){
            succNode.addPred(node);
            node.addSucc(succNode);
         }
      }
   }
   
   
   private void updatePreds(RecursionGraphNode node){
      for(RecursionGraphNode predNode : nodes){
         if(predNode.getSuccElements().contains(node.getProofElement())){
            predNode.addSucc(node);
            node.addPred(predNode);
         }
      }
   }
   
   
   private boolean containsProofElement(ProofElement pe){
      for(RecursionGraphNode node : nodes){
         if(node.getProofElement().equals(pe)){
            return true;
         }
      }
      return false;
   }
   
   private RecursionGraphNode getNode(ProofElement pe){
      for(RecursionGraphNode node : nodes){
         if(node.getProofElement().equals(pe)){
            return node;
         }
      }
      return null;
   }
   
   public LinkedHashSet<RecursionGraphNode> getAllNodes(){
      return nodes;
   }
   
   
   private LinkedHashSet<ProofElement> getSuccElements(ProofElement pe, LinkedList<ProofElement> proofElements){
      LinkedHashSet<ProofElement> succElements = new LinkedHashSet<ProofElement>();
      LinkedHashSet<Contract> contracts = getContractRefsFromProofElement(pe);
      for(Contract contract : contracts){
         ProofElement succElement = getProofElementByContract(contract, proofElements);
         succElements.add(succElement);
      }
      return succElements;
   }
   
   private ProofElement getProofElementByContract(Contract contract, LinkedList<ProofElement> proofElements){
      for(ProofElement pe : proofElements){
         if(pe.getContract().getName().equals(contract.getName())){
            return pe;
         }
      }
      return null;
   }
   
   private LinkedHashSet<Contract> getContractRefsFromProofElement(ProofElement pe){
      LinkedHashSet<Contract> contracts = new LinkedHashSet<Contract>();
      LinkedHashSet<IProofReference<?>> refs = pe.getProofReferences();
      for(IProofReference<?> ref : refs){
         Object target = ref.getTarget();
         if(target instanceof Contract){
            Contract contract = (Contract) target;
            contracts.add(contract);
         }
      }
      return contracts;
   }
   
   
   public LinkedHashSet<ProofElement> findCycles(){
      for(RecursionGraphNode node : nodes){
         cyclingNodes = new LinkedHashSet<RecursionGraphNode>();
         checkNode(node, new LinkedList<RecursionGraphNode>());
      }
      LinkedHashSet<ProofElement> cyclingElements = new LinkedHashSet<ProofElement>();
      for(RecursionGraphNode cycleNode : cyclingNodes){
         cyclingElements.add(cycleNode.getProofElement());
      }
      return cyclingElements;
   }
   
   
   private void checkNode(RecursionGraphNode node, LinkedList<RecursionGraphNode> cycle){
      LinkedHashSet<RecursionGraphNode> succs = node.getSuccs();
      for(RecursionGraphNode succNode : succs){
         if(!cycle.contains(succNode)){
            LinkedList<RecursionGraphNode> newCycle = (LinkedList<RecursionGraphNode>) cycle.clone();
            newCycle.add(succNode);
            checkNode(succNode, newCycle);
         }
         else{
            //cyclefound
            for(RecursionGraphNode newCycleNode : cycle){
               if(!cyclingNodes.contains(newCycleNode)){
                  cyclingNodes.add(newCycleNode);
               }
            }
         }
      }
   }
}
