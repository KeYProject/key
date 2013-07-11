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
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;

import de.uka.ilkd.key.proof.Proof;

/**
 * Provides methods to create and delete all KeY{@link IMarker}.
 * @author Stefan Käsdorf
 */
public class MarkerManager {
   
   public final static String CLOSEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.proofClosedMarker";
   public final static String NOTCLOSEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.proofNotClosedMarker";
   public final static String PROBLEMLOADEREXCEPTIONMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.problemLoaderExceptionMarker";
   public final static String CYCLEDETECTEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.cycleDetectedMarker";
   
   
   /**
    * Creates the {@link MarkerManager#CLOSEDMARKER_ID} or {@link MarkerManager#NOTCLOSEDMARKER_ID} for the given {@link ProofElement}.
    * @param pe - the {@link ProofElement to use.
    * @throws CoreException
    */
   public void setMarker(ProofElement pe) throws CoreException {
      IMarker curMarker = pe.getMarker();
      if(curMarker != null){
         curMarker.delete();
      }
      SourceLocation scl = pe.getSourceLocation();
      Proof proof = pe.getProof();
      IFile javaFile = pe.getJavaFile();
      IFile proofFile = pe.getProofFile();
      if(scl != null){
         if (proof != null && proof.closed()) {
            IMarker marker = javaFile.createMarker(CLOSEDMARKER_ID);
            if (marker.exists()) {
               marker.setAttribute(IMarker.MESSAGE, "Proof closed: " + proofFile.getFullPath());
               marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_INFO);
               marker.setAttribute(IMarker.CHAR_START, scl.getCharStart());
               marker.setAttribute(IMarker.CHAR_END, scl.getCharEnd());
               pe.setMarker(marker);
            }
         }
         else {
            IMarker marker = javaFile.createMarker(NOTCLOSEDMARKER_ID);
            if (marker.exists()) {
               marker.setAttribute(IMarker.MESSAGE, "Proof not closed: " + proofFile.getFullPath());
               marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
               marker.setAttribute(IMarker.CHAR_START, scl.getCharStart());
               marker.setAttribute(IMarker.CHAR_END, scl.getCharEnd());
               pe.setMarker(marker);
            }
         }
      }
   }
   
   
   /**
    * Creates the {@link MarkerManager#CYCLEDETECTEDMARKER_ID} for the given {@ink ProofElement}.
    * @param pe - the {@link ProofElement} to use
    * @throws CoreException
    */
   public void setCycleDetectedMarker(ProofElement pe) throws CoreException{
      IMarker curMarker = pe.getMarker();
      if(curMarker != null){
         curMarker.delete();
      }
      IMarker marker = pe.getJavaFile().createMarker(CYCLEDETECTEDMARKER_ID);
      if (marker.exists()) {
         marker.setAttribute(IMarker.MESSAGE, "Cycle detected");
         marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
         marker.setAttribute(IMarker.CHAR_START, pe.getSourceLocation().getCharStart());
         marker.setAttribute(IMarker.CHAR_END, pe.getSourceLocation().getCharEnd());
         pe.setMarker(marker);
      }
   }
   
   
   /**
    * Creates the ProofLoaderException{@link IMarker} for the given {@link IResource}.
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
    * Searchs the {@link IMarker} int the given {@link IFile} for the given {@link SourceLocation}.
    * @param scl - the {@link SourceLocation} to use
    * @param file - the {@link IFile} to use
    * @return the {@link IMarker} if found. null otherwise
    * @throws CoreException
    */
   public IMarker getMarkerForScl(SourceLocation scl, IFile file) throws CoreException{
      LinkedList<IMarker> markerList = getAllKeYMarker(file);
      for(IMarker marker : markerList){
         Integer startChar = (Integer) marker.getAttribute(IMarker.CHAR_START);
         Integer endChar = (Integer) marker.getAttribute(IMarker.CHAR_END);
         if(scl.getCharStart() == startChar && scl.getCharEnd() == endChar){
            return marker;
         }
      }
      return null;
   }
   
   
   /**
    * Collects all KeY{@link IMarker} for the given {@link IResource}.
    * @param res - the {@link IResource} to use
    * @return a {@link LinkedList} with all KeY{@link IMarker}
    * @throws CoreException
    */
   public LinkedList<IMarker> getAllKeYMarker(IResource res) throws CoreException{
      LinkedList<IMarker> markerList = new LinkedList<IMarker>();
      markerList.addAll(markerArrayToList(res.findMarkers(CLOSEDMARKER_ID, true, IResource.DEPTH_INFINITE)));
      markerList.addAll(markerArrayToList(res.findMarkers(NOTCLOSEDMARKER_ID, true, IResource.DEPTH_INFINITE)));
      markerList.addAll(markerArrayToList(res.findMarkers(PROBLEMLOADEREXCEPTIONMARKER_ID, true, IResource.DEPTH_INFINITE)));
      markerList.addAll(markerArrayToList(res.findMarkers(CYCLEDETECTEDMARKER_ID, true, IResource.DEPTH_INFINITE)));
      return markerList;
   }
   
   
   /**
    * Converts the given {@link IMarker[]} into a {@link LinkedList}.
    * @param markerArr - the {@link IMarker[]} to use
    * @return the {@link LinkedList} with all {@link IMarker} from the array
    */
   private LinkedList<IMarker> markerArrayToList(IMarker[] markerArr){
      LinkedList<IMarker> markerList = new LinkedList<IMarker>();
      for(IMarker marker : markerArr){
         markerList.add(marker);
      }
      return markerList;
   }
   
 
   /**
    * Removes all KeYResource {@link IMarker} from the given {@link IResource}.
    * @param res the {@link IResource} to use
    * @throws CoreException
    */
   public void deleteKeYMarker(IResource res, int depth) throws CoreException{
      res.deleteMarkers(CLOSEDMARKER_ID, true, depth);
      res.deleteMarkers(NOTCLOSEDMARKER_ID, true, depth);
      res.deleteMarkers(PROBLEMLOADEREXCEPTIONMARKER_ID, true, depth);
      res.deleteMarkers(CYCLEDETECTEDMARKER_ID, true, depth);
   }
}
