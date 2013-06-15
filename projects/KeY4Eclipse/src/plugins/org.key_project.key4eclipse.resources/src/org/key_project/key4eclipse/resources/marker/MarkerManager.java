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

package org.key_project.key4eclipse.resources.marker;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;

import de.uka.ilkd.key.proof.Proof;

public class MarkerManager {
   
   public final static String CLOSEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.proofClosedMarker";
   public final static String NOTCLOSEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.proofNotClosedMarker";
   public final static String PROBLEMLOADEREXCEPTIONMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.problemLoaderExceptionMarker";
   
   
   /**
    * Creates the {@link IMarker} for the given {@link Proof} in the given java{@link IFile}.
    * @param proof - the {@link Proof} to use
    * @param scl - the {@link SourceLocation} that provides the start- and end-char for the {@link IMarker}
    * @param javaFile - the java{@link IFile} to create the {@link IMarker} at.
    * @param proofFile - the proof{@link IFile} required to set the {@link IMarker} message
    * @throws CoreException
    */
   public void setMarker(Proof proof, SourceLocation scl, IFile javaFile, IFile proofFile) throws CoreException {
      if (proof.closed()) {
         IMarker marker = javaFile.createMarker(CLOSEDMARKER_ID);
         if (marker.exists()) {
            marker.setAttribute(IMarker.MESSAGE, "Proof closed: " + proofFile.getFullPath());
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_INFO);
            if(scl == null){
               marker.setAttribute(IMarker.LINE_NUMBER, -1);
            }
            else{
               marker.setAttribute(IMarker.CHAR_START, scl.getCharStart());
               marker.setAttribute(IMarker.CHAR_END, scl.getCharEnd());
            }
         }
      }
      else {
         IMarker marker = javaFile.createMarker(NOTCLOSEDMARKER_ID);
         if (marker.exists()) {
            marker.setAttribute(IMarker.MESSAGE, "Proof not closed: " + proofFile.getFullPath());
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
            if(scl == null){
               marker.setAttribute(IMarker.LINE_NUMBER, -1);
            }
            else{
               marker.setAttribute(IMarker.CHAR_START, scl.getCharStart());
               marker.setAttribute(IMarker.CHAR_END, scl.getCharEnd());
            }
         }
      }
   }
   
   
   /**
    * Sets the ProofLoaderException{@link IMarker} for the given {@link IResource}.
    * @param res - the {@link IResource} to use
    * @throws CoreException
    */
   public void setProblemLoaderExceptionMarker(IProject project, String msg) throws CoreException{
      IMarker marker = project.createMarker(PROBLEMLOADEREXCEPTIONMARKER_ID);
      if (marker.exists()) {
         marker.setAttribute(IMarker.MESSAGE, msg);
         marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
      }
   }
   
   
   /**
    * Removes all KeYResource {@link IMarker} from the given {@link IFile}.
    * @param res the {@link IResource} to use
    * @throws CoreException
    */
   public void deleteKeYMarker(IResource res) throws CoreException{
      res.deleteMarkers(CLOSEDMARKER_ID, true, IResource.DEPTH_INFINITE);
      res.deleteMarkers(NOTCLOSEDMARKER_ID, true, IResource.DEPTH_INFINITE);
      res.deleteMarkers(PROBLEMLOADEREXCEPTIONMARKER_ID, true, IResource.DEPTH_INFINITE);
   }

   
   /**
    * Removes all KeYResource {@link IMarker} from the {@link IFile}s of the given {@link LinkedList}.
    * @param files - the given {@link LinkedList}
    * @throws CoreException
    */
   public void deleteKeYMarker(LinkedList<IFile> files) throws CoreException{
      for(IFile file : files){
         deleteKeYMarker(file);
      }
   }
}