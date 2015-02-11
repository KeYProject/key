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
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * DeltaVisitor to visit every child of the given delta and extract KeY Project relevant changes.
 * @author Stefan Käsdorf
 */
public class KeYProjectDeltaVisitor implements IResourceDeltaVisitor{

   private Set<IFile> changedJavaFiles;
   private Set<IFile> changedProofAndMetaFiles;
   
   public KeYProjectDeltaVisitor() {
      this.changedJavaFiles = new LinkedHashSet<IFile>();
      this.changedProofAndMetaFiles = new LinkedHashSet<IFile>();
   }
   
   public Set<IFile> getChangedJavaFiles(){
      return changedJavaFiles;
   }

   public Set<IFile> getChangedProofAndMetaFiles(){
      return changedProofAndMetaFiles;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(IResourceDelta delta) {
      IResource deltaRes = delta.getResource();
      if(deltaRes != null && IResource.FILE == deltaRes.getType()){
         IFile deltaFile = (IFile) deltaRes;
         if(KeYResourcesUtil.isJavaFileAndInSrcFolder(deltaFile)){
            changedJavaFiles.add(deltaFile);
         }
         else if(KeYResourcesUtil.isInProofFolder(deltaRes) 
               && KeYResourcesUtil.PROOF_FILE_EXTENSION.equals(deltaRes.getFileExtension()) || KeYResourcesUtil.META_FILE_EXTENSION.equals(deltaRes.getFileExtension())){
            changedProofAndMetaFiles.add(deltaFile);
         }
      }
      return true;
   }
}