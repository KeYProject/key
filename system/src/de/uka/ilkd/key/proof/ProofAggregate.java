// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofStatus;

public abstract class ProofAggregate {

   private String name;

   protected ProofAggregate(String name) {
      this.name = name;
   }

   public static ProofAggregate createProofAggregate(ProofAggregate[] proofs, String name) {
      if (proofs.length>1) {            
         return new CompoundProof(proofs, name);
      } else {
         return proofs[0];
      }
   }

   public static ProofAggregate createProofAggregate(Proof[] proofs, String name) {
      if (proofs.length==0) return null; // needed for tests
      if (proofs.length>1) {
         SingleProof singles[] = new SingleProof[proofs.length];
         for (int i=0; i<proofs.length; i++) {
            singles[i] = new SingleProof(proofs[i], name);
         }
         return new CompoundProof(singles, name);
      } else {
         return new SingleProof(proofs[0], name);
      }
   }

   public static ProofAggregate createProofAggregate(Proof proof, String name) {
      return new SingleProof(proof, name);
   }

   public abstract Proof[] getProofs();

   public Proof getFirstProof() {
      return getProofs() != null && getProofs().length >= 1 ? getProofs()[0] : null;
   }

   public void setProofEnv(ProofEnvironment env) {
      Proof[] proofs = getProofs();
      for (Proof proof : proofs) {
         proof.setEnv(env);
      }
   }

   public abstract int size();

   public String description() {
      return name;
   }
   
   @Override
   public boolean equals(Object o) {
      if (o == null || o.getClass() != this.getClass()) {
         return false;
      }
      final ProofAggregate other = (ProofAggregate) o;
      
      return size() == other.size() && name.equals(other.name);
   }

   @Override
   public int hashCode() {
      return 7*size() + 17*name.hashCode();
   }
   
   public String toString() {	
      return name;
   }   

   public abstract ProofStatus getStatus();

   public abstract ProofAggregate[] getChildren();

   public Proof getProof(int proofNum) {
      return getProofs()[proofNum];
   }
}