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
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.io.ProofMetaFileTypeElement;
import org.key_project.key4eclipse.resources.marker.MarkerUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;

import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
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
   
   private IFolder proofFolder;
   private IFile proofFile;
   private IFile metaFile;
   private String proofFileMD5;

   private boolean build;
   private boolean outdated;
   
   private IMarker proofMarker;
   private List<IMarker> recursionMarker;
   private String markerMsg;
   
   private KeYEnvironment<CustomUserInterface> environment;
   private Contract contract;
   private ProofOblInput proofObl;
   private boolean proofClosed;
   private LinkedHashSet<IProofReference<?>> proofReferences;
   private List<IFile> usedContracts;
   private List<String> calledMethods;

   private List<ProofMetaFileTypeElement> typeElements;
   
   private final SpecificationRepository specificationRepository;
   
   public ProofElement(IFile javaFile, SourceLocation scl , KeYEnvironment<CustomUserInterface> environment, IFolder proofFolder, IFile proofFile, IFile metaFile, IMarker proofMarker, List<IMarker> recursionMarker, Contract contract){
      this.javaFile = javaFile;
      this.scl = scl;

      this.proofFolder = proofFolder;
      this.proofFile = proofFile;
      this.metaFile = metaFile;
      
      this.build = false;
      this.outdated = false;
      
      this.proofMarker = proofMarker;
      this.recursionMarker = recursionMarker;
      
      this.environment = environment;
      this.contract = contract;
      this.proofObl = null;
      
      this.proofReferences = new LinkedHashSet<IProofReference<?>>();
      
      this.proofFileMD5 = null;
      this.markerMsg = null;
      this.proofClosed = false;
      this.usedContracts = new LinkedList<IFile>();
      this.typeElements = new LinkedList<ProofMetaFileTypeElement>();
      this.specificationRepository = environment.getSpecificationRepository();
      init();
   }
   
   
   private void init() {
      if(hasMetaFile()){
         try{
            ProofMetaFileReader pmfr = new ProofMetaFileReader(metaFile);
            this.proofFileMD5 = pmfr.getProofFileMD5();
            this.outdated = pmfr.getProofOutdated();
            this.markerMsg = pmfr.getMarkerMessage();
            this.proofClosed = pmfr.getProofClosed();
            this.usedContracts = pmfr.getUsedContracts();
            this.typeElements = pmfr.getTypeElements();

            if(!hasMarker()){
               MarkerUtil.setMarker(this);
            }
         }
         catch(Exception e){
            outdated = true;
         }
      }
      else{
         outdated = !hasProofFile() || !hasMetaFile() || !hasMarker();
      }
   }
   

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
   public IFile getMetaFile(){
      return metaFile;
   }
   public String getMD5() {
      return proofFileMD5;
   }

   public boolean getBuild(){
      return build;
   }
   public void setBuild(boolean build){
      this.build = build;
   }
   public boolean getOutdated(){
      return outdated;
   }
   public void setOutdated(boolean outdated){
      this.outdated = outdated;
   }
   
   
   public IMarker getProofMarker(){
      return proofMarker;
   }
   public void setProofMarker(IMarker proofMarker){
      this.proofMarker = proofMarker;
   }
   public List<IMarker> getRecursionMarker(){
      return recursionMarker;
   }
   public void setRecursionMarker(LinkedList<IMarker> recursionMarker){
      this.recursionMarker = recursionMarker;
   }
   public void addRecursionMarker(IMarker recursionMarker){
      this.recursionMarker.add(recursionMarker);
   }
   public String getMarkerMsg() {
      return markerMsg;
   }
   public void setMarkerMsg(String markerMsg) {
      this.markerMsg = markerMsg;
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
   public List<IFile> getUsedContracts() {
      return usedContracts;
   }
   public void setUsedContracts(List<IFile> usedContracts) {
      this.usedContracts = usedContracts;
   }

   public List<ProofMetaFileTypeElement> getTypeElements() {
      return typeElements;
   }
   
   public List<String> getCalledMethods() {
      return calledMethods;
   }

   public void setCalledMethods(List<String> calledMethods) {
      this.calledMethods = calledMethods;
   }

   @Override
   public String toString(){
      return contract.getName();
   }
   
   
   public boolean hasProofFile(){
      return (proofFile != null && proofFile.exists());
   }
   
   
   public boolean hasMetaFile(){
      return (metaFile != null && metaFile.exists());
   }
   
   
   public boolean hasMarker(){
      if(proofMarker != null && proofMarker.exists()){
         return true;
      }
      if(recursionMarker != null && !recursionMarker.isEmpty()){
         for(IMarker marker : recursionMarker){
            if(marker != null && marker.exists()){
               return true;
            }
         }
      }
      return false;
   }
   
   
   public boolean hasProofMarker(){
      if(proofMarker != null && proofMarker.exists()){
         return true;
      }
      return false;
   }
   
   
   public boolean hasRecursionMarker(){
      if(recursionMarker != null && !recursionMarker.isEmpty()){
         for(IMarker marker : recursionMarker){
            if(marker != null && marker.exists()){
               return true;
            }
         }
      }
      return false;
   }


   public SpecificationRepository getSpecificationRepository() {
      return specificationRepository;
   }
}