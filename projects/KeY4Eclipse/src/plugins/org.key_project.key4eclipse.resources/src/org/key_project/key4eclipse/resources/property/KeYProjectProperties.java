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

package org.key_project.key4eclipse.resources.property;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;

/**
 * Properties for the ProofManagementPropertyPage.
 * @author Stefan Käsdorf
 */
public final class KeYProjectProperties {
   
   public static final QualifiedName PROP_ENABLE_BUILD_PROOFS = new QualifiedName("org.key_project.key4eclipse.resources", "buildProofs");
   public static final QualifiedName PROP_ENALBLE_BUILD_REQUIRED_PROOFS_ONLY = new QualifiedName("org.key_project.key4eclipse.resources", "buildRequiredProofsOnly");
   public static final QualifiedName PROP_ENABLE_MULTITHREADING = new QualifiedName("org.key_project.key4eclipse.resources", "enableMultiThreading");
   public static final QualifiedName PROP_NUMBER_OF_THREADS = new QualifiedName("org.key_project.key4eclipse.resources", "numberOfThreads");
   public static final QualifiedName PROP_AUTO_DELETE_PROOFFILES = new QualifiedName("org.key_project.key4eclipse.resources", "autoDeleteProofFiles");
   public static final QualifiedName PROP_HIDE_META_FILES = new QualifiedName("org.key_project.key4eclipse.resources", "hideMetaFiles");
   
   
   public static boolean isEnableBuildProofs(IProject project) throws CoreException {
      if (project != null) {
         String value = project.getPersistentProperty(PROP_ENABLE_BUILD_PROOFS);
         if(value == null){
            return true;
         }
         else return Boolean.parseBoolean(value);
      }
      else {
         return false;
      }
   }
   
   public static void setEnableBuildProofs(IProject project,  boolean enabled) throws CoreException {
      if (project != null) {
         project.setPersistentProperty(PROP_ENABLE_BUILD_PROOFS, enabled + "");
      }
   }
   
   
   public static boolean isEnableBuildRequiredProofsOnly(IProject project) throws CoreException {
      if (project != null) {
         String value = project.getPersistentProperty(PROP_ENALBLE_BUILD_REQUIRED_PROOFS_ONLY);
         if(value == null){
            return true;
         }
         else return Boolean.parseBoolean(value);
      }
      else {
         return false;
      }
   }
   
   public static void setEnableBuildProofsEfficient(IProject project,  boolean enabled) throws CoreException {
      if (project != null) {
         project.setPersistentProperty(PROP_ENALBLE_BUILD_REQUIRED_PROOFS_ONLY, enabled + "");
      }
   }
   
   
   public static boolean isEnableMultiThreading(IProject project) throws CoreException {
      if (project != null) {
         String value = project.getPersistentProperty(PROP_ENABLE_MULTITHREADING);
         if(value == null){
            return true;
         }
         else{
            return Boolean.parseBoolean(value);
         }
      }
      else {
         return false;
      }
   }
   
   public static void setEnableMultiThreading(IProject project,  boolean enabled) throws CoreException {
      if (project != null) {
         project.setPersistentProperty(PROP_ENABLE_MULTITHREADING, enabled + "");
      }
   }
   
   
   public static int getNumberOfThreads(IProject project) throws CoreException {
      if (project != null) {
         try{
            return Integer.parseInt(project.getPersistentProperty(PROP_NUMBER_OF_THREADS));
         }
         catch (NumberFormatException e) {
            return 2;
         }
      }
      else {
         return 0;
      }
   }
   
   public static void setNumberOfThreads(IProject project,  String number) throws CoreException {
      if (project != null) {
         project.setPersistentProperty(PROP_NUMBER_OF_THREADS, number);
      }
   }
   
   
   public static boolean isAutoDeleteProofFiles(IProject project) throws CoreException {
      if (project != null) {
         String value = project.getPersistentProperty(PROP_AUTO_DELETE_PROOFFILES);
         if(value == null){
            return true;
         }
         else{
            return Boolean.parseBoolean(value); 
         }
      }
      else {
         return false;
      }
   }
   
   
   public static void setAutoDeleteProofFiles(IProject project,  boolean enabled) throws CoreException {
      if (project != null) {
         project.setPersistentProperty(PROP_AUTO_DELETE_PROOFFILES, enabled + "");
      }
   }
   
   
   public static boolean isHideMetaFiles(IProject project) throws CoreException {
      if (project != null) {
         String value = project.getPersistentProperty(PROP_HIDE_META_FILES);
         if(value == null){
            return false;
         }
         else{
            return Boolean.parseBoolean(value);
         }
      }
      else {
         return false;
      }
   }
   
   
   public static void setHideMetaFiles(IProject project,  boolean enabled) throws CoreException {
      if (project != null) {
         project.setPersistentProperty(PROP_HIDE_META_FILES, enabled + "");
      }
   }
}