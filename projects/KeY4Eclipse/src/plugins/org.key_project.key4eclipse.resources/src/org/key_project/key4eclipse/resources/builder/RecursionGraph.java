package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedHashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.Contract;

/**
 * The Recursiongraph to identify recursion cycles.
 * @author Stefan Käsdorf
 */
public class RecursionGraph {
   
   private LinkedHashSet<RecursionGraphNode> nodes;
   private LinkedList<ProofElement> proofElements;
   private LinkedHashSet<LinkedList<RecursionGraphNode>> tmpNodeCycles;

   
   /**
    * The Constructor that creates the whole graph for the given {@link LinkedList} of {@link ProofElement}s.
    * @param proofElements - the {@link ProofElement}s to use
    */
   public RecursionGraph(LinkedList<ProofElement> proofElements){
      nodes = new LinkedHashSet<RecursionGraphNode>();
      tmpNodeCycles = new LinkedHashSet<LinkedList<RecursionGraphNode>>();
      this.proofElements = proofElements;
      for(ProofElement pe : this.proofElements){
         addProofElement(pe);
      }
   }
   
   
   /**
    * Adds the given {@link ProofElement} to the graph
    * @param pe - the {@link ProofElement} to add
    */
   private void addProofElement(ProofElement pe){
      RecursionGraphNode node = new RecursionGraphNode(pe, getSuccElements(pe, proofElements));
      addNode(node);
   }
   
   
   /**
    * Adds the given {@link RecursionGraphNode} to the graph
    * @param node - the {@link RecursionGraphNode} to add
    */
   private void addNode(RecursionGraphNode node){
      updatePreds(node);
      updateSuccs(node);
      nodes.add(node);
   }
   
   
   /**
    * Updates the successors of all {@link RecursionGraphNode}s of the graph.
    * @param node - the new {@link RecursionGraphNode}
    */
   private void updateSuccs(RecursionGraphNode node){
      for(RecursionGraphNode succNode : nodes){
         if(node.getSuccElements().contains(succNode.getProofElement())){
            succNode.addPred(node);
            node.addSucc(succNode);
         }
      }
   }
   
   
   /**
    * Updates the predecessors of all {@link RecursionGraphNode}s of the graph.
    * @param node - the new {@link RecursionGraphNode}
    */
   private void updatePreds(RecursionGraphNode node){
      for(RecursionGraphNode predNode : nodes){
         if(predNode.getSuccElements().contains(node.getProofElement())){
            predNode.addSucc(node);
            node.addPred(predNode);
         }
      }
   }
   
   
   /**
    * Returns the successor {@link ProofElement}s for the {@link RecursionGraphNode} of the given {@link ProofElement}.
    * @param pe - the {@link ProofElement} to use
    * @param proofElements - all {@link ProofElement}s
    * @return the successors
    */
   private LinkedHashSet<ProofElement> getSuccElements(ProofElement pe, LinkedList<ProofElement> proofElements){
      LinkedHashSet<ProofElement> succElements = new LinkedHashSet<ProofElement>();
      LinkedHashSet<Contract> contracts = getContractRefsFromProofElement(pe);
      for(Contract contract : contracts){
         ProofElement succElement = getProofElementByContract(contract, proofElements);
         succElements.add(succElement);
      }
      return succElements;
   }
   
   
   /**
    * Returns the {@link ProofElement} that belongs to the given {@link Contract}.
    * @param contract - the {@link Contract} to use
    * @param proofElements - all {@link ProofElement}s
    * @return the {@link ProofElement} for the given {@link Contract}
    */
   private ProofElement getProofElementByContract(Contract contract, LinkedList<ProofElement> proofElements){
      for(ProofElement pe : proofElements){
         if(pe.getContract().getName().equals(contract.getName())){
            return pe;
         }
      }
      return null;
   }
   
   
   /**
    * Collects all {@link IProofReference}s from the type {@link Contract} for the given {@link ProofElement}.
    * @param pe - the {@link ProofElement} to use.
    * @return the {@link LinkedList} with the collected {@link Contract}ss
    */
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
   
   
   /**
    * Checks the whole graph for cycles and returns all {@link ProofElement} which are part of a cycle.
    * @return all cycling {@link ProofElement}s
    */
   public LinkedHashSet<LinkedList<ProofElement>> findCycles(){
      LinkedHashSet<LinkedList<ProofElement>> cycles = new LinkedHashSet<LinkedList<ProofElement>>();
      LinkedList<RecursionGraphNode> checkedNodes = new LinkedList<RecursionGraphNode>();
      for(RecursionGraphNode node : nodes){
         if(!checkedNodes.contains(node)){
            tmpNodeCycles = new LinkedHashSet<LinkedList<RecursionGraphNode>>();
            searchCycle(node, new LinkedList<RecursionGraphNode>());
            for(LinkedList<RecursionGraphNode> tmpNodeCycle : tmpNodeCycles){
               LinkedList<ProofElement> peCycle = new LinkedList<ProofElement>();
               for(RecursionGraphNode tmpCycleNode : tmpNodeCycle){
                  peCycle.add(tmpCycleNode.getProofElement());
                  if(!checkedNodes.contains(tmpCycleNode)){
                     checkedNodes.add(tmpCycleNode);
                  }
               }
               cycles.add(peCycle);
               cycles.addAll(rotateCycle(peCycle));
            }
         }
      }
      return cycles;
   }
   
   
   /**
    * Rotates the given cycle and return a hashSet with all possible cycles.
    * @param cycle - the cycle to rotate
    * @return all cycles
    */
   private LinkedHashSet<LinkedList<ProofElement>> rotateCycle(LinkedList<ProofElement> cycle){
      LinkedHashSet<LinkedList<ProofElement>> rotatedCycles = new LinkedHashSet<LinkedList<ProofElement>>();
      for(int i = 1; i < cycle.size(); i++){
         rotatedCycles.add(rotateCycleByTimes(cycle, i));
      }
      return rotatedCycles;
   }
   
   
   /**
    * Rotates respectively shifts the given cycle by the given number.
    * @param cycle - the cycle to rotate
    * @param number - the number of shifts
    * @return
    */
   private LinkedList<ProofElement> rotateCycleByTimes(LinkedList<ProofElement> cycle, int number){
      LinkedList<ProofElement> rotatedCycle = new LinkedList<ProofElement>();
      for(int i = 0; i < cycle.size(); i++){
         int current = i + number;
         if(current < cycle.size()){
            rotatedCycle.add(cycle.get(current));
         }
         else {
            current = current % cycle.size();
            rotatedCycle.add(cycle.get(current));
         }
      }
      return rotatedCycle;
   }
   
   
   /**
    * Checks if the given {@link RecursionGraphNode} is part of a cycle
    * @param node
    * @param cycle
    */
   private void searchCycle(RecursionGraphNode node, LinkedList<RecursionGraphNode> cycle){
      LinkedList<RecursionGraphNode> newCycle = cloneLinkedList(cycle);
      newCycle.add(node);
      LinkedHashSet<RecursionGraphNode> succs = node.getSuccs();
      for(RecursionGraphNode succNode : succs){
         if(!cycle.contains(succNode)){
            searchCycle(succNode, newCycle);
         }
         else{
            //cycle found
            while(newCycle.get(0) != succNode){
               newCycle.remove(0);
            }
            tmpNodeCycles.add(newCycle);
         }
      }
   }
   
   
   /**
    * Clones the given {@link LinkedList} of {@link RecursionGraphNode}s.
    * @param nodes - the {@link LinkedList} to clone
    * @return the cloned {@link LinkedList}
    */
   private LinkedList<RecursionGraphNode> cloneLinkedList(LinkedList<RecursionGraphNode> nodes){
      LinkedList<RecursionGraphNode> clone = new LinkedList<RecursionGraphNode>();
      for(RecursionGraphNode node : nodes){
         clone.add(node);
      }
      return clone;
   }
}
