/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedHashSet;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class ProofElement {

   private IFile javaFile;
   private SourceLocation scl;
   
   private IFolder proofFolder;
   private IFile proofFile;
   
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   private Contract contract;
   private ProofOblInput proofObl;
   
   private Proof proof;
   
   private LinkedHashSet<IProofReference<?>> proofReferences;
   private KeYJavaType kjt;
   
   

   public IFile getJavaFile() {
      return javaFile;
   }
   public SourceLocation getSourceLocation() {
      return scl;
   }
   
   public IFolder getProofFolder(){
      return proofFolder;
   }
   public IFile getProofFile(){
      return proofFile;
   }
   
   public KeYEnvironment<CustomConsoleUserInterface> getKeYEnvironment(){
      return environment;
   }
   
   public void setKeYEnvironment(KeYEnvironment<CustomConsoleUserInterface> environment){
      this.environment = environment;
   }

   
   public Contract getContract(){
      return contract;
   }
   public void setContracts(Contract contract){
      this.contract = contract;
   } 
   public ProofOblInput getProofObl() {
      return proofObl;
   }
   public void setProofObl(ProofOblInput proofObl){
      this.proofObl = proofObl;
   }

   
   public Proof getProof(){
      return proof;
   }
   public void setProof(Proof proof){
      this.proof = proof;
   }
   
   
   public LinkedHashSet<IProofReference<?>> getProofReferences(){
      return proofReferences;
   }
   public void setProofReferences(LinkedHashSet<IProofReference<?>> proofReferences){
      this.proofReferences = proofReferences;
   }
   public KeYJavaType getKeYJavaType(){
      return kjt;
   } 
   
   
   public ProofElement(ProofOblInput obl, IFile javaFile, SourceLocation scl, KeYEnvironment<CustomConsoleUserInterface> environment, IFolder proofFolder, IFile proofFile, KeYJavaType kjt, Contract contract){
      this.javaFile = javaFile;
      this.scl = scl;
      
      this.proofFolder = proofFolder;
      this.proofFile = proofFile;
      
      this.environment = environment;
      
      this.contract = contract;
      this.proofObl = obl;
      
      this.proof = null;
      
      this.proofReferences = new LinkedHashSet<IProofReference<?>>();
      this.kjt = kjt;
   }
}