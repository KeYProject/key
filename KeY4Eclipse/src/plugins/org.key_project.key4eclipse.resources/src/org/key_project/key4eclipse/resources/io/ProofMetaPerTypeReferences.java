package org.key_project.key4eclipse.resources.io;

import java.util.LinkedList;
import java.util.List;

import org.key_project.key4eclipse.resources.builder.ProofElement;

/**
 * Creates the representation of all references used by a particular {@link ProofElement}
 * @author Stefan Käsdorf
 */
public class ProofMetaPerTypeReferences {

   private List<ProofMetaReferenceAxiom> axioms;
   private List<ProofMetaReferenceInvariant> invariants;
   private List<ProofMetaReferenceAccess> accesses;
   private List<ProofMetaReferenceMethod> inlineMethods;
   private List<ProofMetaReferenceContract> contracts;
   
   public ProofMetaPerTypeReferences(){
      this.axioms = new LinkedList<ProofMetaReferenceAxiom>();
      this.invariants = new LinkedList<ProofMetaReferenceInvariant>();
      this.accesses = new LinkedList<ProofMetaReferenceAccess>();
      this.inlineMethods = new LinkedList<ProofMetaReferenceMethod>();
      this.contracts = new LinkedList<ProofMetaReferenceContract>();
   }

   public List<ProofMetaReferenceAxiom> getAxioms() {
      return axioms;
   }
   public void addAxiom(ProofMetaReferenceAxiom axiom){
      axioms.add(axiom);
   }

   public List<ProofMetaReferenceInvariant> getInvariants() {
      return invariants;
   }
   public void addInvariant(ProofMetaReferenceInvariant invariant){
      invariants.add(invariant);
   }

   public List<ProofMetaReferenceAccess> getAccesses() {
      return accesses;
   }
   public void addAccess(ProofMetaReferenceAccess access){
      accesses.add(access);
   }

   public List<ProofMetaReferenceMethod> getInlineMethods() {
      return inlineMethods;
   }
   public void addInlineMethod(ProofMetaReferenceMethod inlineMethod) {
      inlineMethods.add(inlineMethod);
   }

   public List<ProofMetaReferenceContract> getContracts() {
      return contracts;
   }
   public void addContract(ProofMetaReferenceContract contract) {
     contracts.add(contract);
   }
   
}
