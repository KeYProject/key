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

package org.key_project.key4eclipse.resources.property;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;

public final class KeYProjectProperties {
   
   public static final QualifiedName PROP_BUILD_PROOFS = new QualifiedName("org.key_project.key4eclipse.resources", "buildProofs");
   public static final QualifiedName PROP_ENALBLE_EFFICIENT_PROOFMANAGEMENT = new QualifiedName("org.key_project.key4eclipse.resources", "enableEfficientProofManagement");
   public static final QualifiedName PROP_AUTO_DELETE_PROOFFILES = new QualifiedName("org.key_project.key4eclipse.resources", "autoDeleteProofFiles");
   public static final QualifiedName PROP_HIDE_META_FILES = new QualifiedName("org.key_project.key4eclipse.resources", "hideMetaFiles");
   
   
   public static boolean isBuildProofs(IProject project) throws CoreException {
      if (project != null) {
         return Boolean.parseBoolean(project.getPersistentProperty(PROP_BUILD_PROOFS));
      }
      else {
         return false;
      }
   }
   
   public static void setBuildProofs(IProject project,  boolean enabled) throws CoreException {
      if (project != null) {
         project.setPersistentProperty(PROP_BUILD_PROOFS, enabled + "");
      }
   }
   
   
   public static boolean isEnableEfficientProofManagement(IProject project) throws CoreException {
      if (project != null) {
         return Boolean.parseBoolean(project.getPersistentProperty(PROP_ENALBLE_EFFICIENT_PROOFMANAGEMENT));
      }
      else {
         return false;
      }
   }
   
   public static void setEnableEfficientProofManagement(IProject project,  boolean enabled) throws CoreException {
      if (project != null) {
         project.setPersistentProperty(PROP_ENALBLE_EFFICIENT_PROOFMANAGEMENT, enabled + "");
      }
   }
   
   
   public static boolean isAutoDeleteProofFiles(IProject project) throws CoreException {
      if (project != null) {
         return Boolean.parseBoolean(project.getPersistentProperty(PROP_AUTO_DELETE_PROOFFILES));
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
         return Boolean.parseBoolean(project.getPersistentProperty(PROP_HIDE_META_FILES));
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