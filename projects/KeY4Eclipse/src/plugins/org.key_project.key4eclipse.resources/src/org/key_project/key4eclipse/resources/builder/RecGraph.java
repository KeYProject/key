package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedHashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.Contract;

public class RecGraph {

   private LinkedList<RecNode> nodes = new LinkedList<RecNode>();
   private LinkedList<ProofElement> proofElements;
   public RecGraph(LinkedList<ProofElement> proofElements){
      this.proofElements = proofElements;
      for(ProofElement pe : this.proofElements){
         if(pe.getProofDone()){
            LinkedHashSet<ProofElement> succElements = getSuccElementsForProofElement(pe);
            nodes.add(new RecNode(pe, succElements));
         }
         else{
            //nutze refs auf metadateien
         }
      }
   }
   
   
   /**
    * Returns the successor {@link ProofElement}s for the {@link RecursionGraphNode} of the given {@link ProofElement}.
    * @param pe - the {@link ProofElement} to use
    * @param proofElements - all {@link ProofElement}s
    * @return the successors
    */
   private LinkedHashSet<ProofElement> getSuccElementsForProofElement(ProofElement pe){
      LinkedHashSet<ProofElement> succElements = new LinkedHashSet<ProofElement>();
      LinkedHashSet<Contract> contracts = getContractRefsFromProofElement(pe);
      for(Contract contract : contracts){
         ProofElement succElement = getProofElementByContract(contract, proofElements);
         succElements.add(succElement);
      }
      return succElements;
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
}