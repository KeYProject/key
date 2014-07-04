/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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
import org.eclipse.core.resources.IMarker;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;

import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Object that represents a proof and provides all the required stuff for the build process.
 * @author Stefan Käsdorf
 */
public class ProofElement {

   private IFile javaFile;
   private SourceLocation scl;
   private LinkedHashSet<IMarker> marker;
   private String markerMsg;
   
   private IFolder proofFolder;
   private IFile proofFile;
   private IFile metaFile;
   
   private KeYEnvironment<CustomUserInterface> environment;
   
   private Contract contract;
   private ProofOblInput proofObl;
   
   private boolean proofClosed;
   
   private LinkedHashSet<IProofReference<?>> proofReferences;
   private LinkedList<ProofElement> usedContracts;
   
   

   public IFile getJavaFile() {
      return javaFile;
   }
   public SourceLocation getSourceLocation() {
      return scl;
   }
   
   public LinkedHashSet<IMarker> getMarker(){
      return marker;
   }
   public void setMarker(LinkedHashSet<IMarker> marker){
      this.marker = marker;
   }
   public void addMarker(IMarker marker){
      this.marker.add(marker);
   }
   public void removeMarker(IMarker marker){
      this.marker.remove(marker);
   }
   
   public String getMarkerMsg() {
      return markerMsg;
   }
   public void setMarkerMsg(String markerMsg) {
      this.markerMsg = markerMsg;
   }
   
   public IFolder getProofFolder(){
      return proofFolder;
   }
   public IFile getProofFile(){
      return proofFile;
   }
   public IFile getMetaFile(){
      return metaFile;
   }
   
   public KeYEnvironment<CustomUserInterface> getKeYEnvironment(){
      return environment;
   }
   public void setKeYEnvironment(KeYEnvironment<CustomUserInterface> environment){
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

   
   public boolean getProofClosed(){
      return proofClosed;
   }
   public void setProofClosed(boolean proofStatus){
      this.proofClosed = proofStatus;
   }
   
   
   public LinkedHashSet<IProofReference<?>> getProofReferences(){
      return proofReferences;
   }
   public void setProofReferences(LinkedHashSet<IProofReference<?>> proofReferences){
      this.proofReferences = proofReferences;
   }
   public LinkedList<ProofElement> getUsedContracts() {
      return usedContracts;
   }
   public void setUsedContracts(LinkedList<ProofElement> usedContracts) {
      this.usedContracts = usedContracts;
   }
   
   public ProofElement(IFile javaFile, SourceLocation scl , KeYEnvironment<CustomUserInterface> environment, IFolder proofFolder, IFile proofFile, IFile metaFile, LinkedHashSet<IMarker> marker, Contract contract){
      this.javaFile = javaFile;
      this.scl = scl;
      this.marker = marker;
      
      this.proofFolder = proofFolder;
      this.proofFile = proofFile;
      this.metaFile = metaFile;
      
      this.environment = environment;
      
      this.contract = contract;
      
      this.proofReferences = new LinkedHashSet<IProofReference<?>>();
      this.usedContracts = new LinkedList<ProofElement>();
   }
   
   @Override
   public String toString(){
      return contract.getName();
   }
}