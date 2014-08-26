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

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * DeltaVisitor to visit every child of the given delta and extract KeY Project relevant changes.
 * @author Stefan Käsdorf
 */
public class KeYProjectDeltaVisitor implements IResourceDeltaVisitor{

   private List<IFile> changedJavaFiles;
   private List<IFile> changedProofAndMetaFiles;
   
   public KeYProjectDeltaVisitor(IProject project) {
      this.changedJavaFiles = new LinkedList<IFile>();
      this.changedProofAndMetaFiles = new LinkedList<IFile>();
   }

   public List<IFile> getChangedJavaFiles(){
      return changedJavaFiles;
   }
   
   public List<IFile> getChangedProofAndMetaFiles(){
      return changedProofAndMetaFiles;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(IResourceDelta delta) {
      IResource deltaRes = delta.getResource();
      if(IResource.FILE == deltaRes.getType()){
         if(KeYResourcesUtil.isJavaFileAndInSrcFolder(deltaRes)){
            if(IResourceDelta.ADDED == delta.getKind() || IResourceDelta.CHANGED == delta.getKind() || IResourceDelta.REMOVED == delta.getKind()){
               if(!changedJavaFiles.contains(deltaRes)){
                  changedJavaFiles.add((IFile) deltaRes);
               }
            }
         }
         else if(KeYResourcesUtil.isInProofFolder(deltaRes)){
            if (KeYResourcesUtil.PROOF_FILE_EXTENSION.equals(deltaRes.getFileExtension()) ||
                KeYResourcesUtil.META_FILE_EXTENSION.equals(deltaRes.getFileExtension())) {
               if(!changedProofAndMetaFiles.contains(deltaRes)){
                  changedProofAndMetaFiles.add((IFile) deltaRes);
               }
            }
         }
      }
      return true;
   }
}