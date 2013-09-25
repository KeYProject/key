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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Object that represents a proof and provides all the required stuff for the build process.
 * @author Stefan Käsdorf
 */
public class ProofElement {

   private IFile javaFile;
   private SourceLocation scl;
   private IMarker marker;
   
   private IFolder proofFolder;
   private IFile proofFile;
   private IFile metaFile;
   
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   private Contract contract;
   private ProofOblInput proofObl;
   
   private Proof proof;
   
   private LinkedHashSet<IProofReference<?>> proofReferences;
   
   

   public IFile getJavaFile() {
      return javaFile;
   }
   public SourceLocation getSourceLocation() {
      return scl;
   }
   public IMarker getMarker(){
      return marker;
   }
   public void setMarker(IMarker marker){
      this.marker = marker;
   }
   
   public IFolder getProofFolder(){
      return proofFolder;
   }
   public IFile getProofFile(){
      return proofFile;
   }
   public void setProofFile(IFile proofFile){
      this.proofFile = proofFile;
   }
   public IFile getMetaFile(){
      return metaFile;
   }
   public void setMetaFile(IFile metaFile){
      this.metaFile = metaFile;
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
   
   
   public ProofElement(IFile javaFile, SourceLocation scl , KeYEnvironment<CustomConsoleUserInterface> environment, IFolder proofFolder, Contract contract){
      this.javaFile = javaFile;
      this.scl = scl;
      
      this.proofFolder = proofFolder;
      
      this.environment = environment;
      
      this.contract = contract;
      
      this.proof = null;
      
      this.proofReferences = new LinkedHashSet<IProofReference<?>>();
   }
}