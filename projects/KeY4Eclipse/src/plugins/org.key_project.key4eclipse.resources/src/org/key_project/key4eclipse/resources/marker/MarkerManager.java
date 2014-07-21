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

package org.key_project.key4eclipse.resources.marker;

import java.util.LinkedHashSet;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;
import org.key_project.util.java.StringUtil;

/**
 * Provides methods to create and delete all KeY{@link IMarker}.
 * @author Stefan Käsdorf
 */
public class MarkerManager {
   
   public final static String CLOSEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.proofClosedMarker";
   public final static String NOTCLOSEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.proofNotClosedMarker";
   public final static String PROBLEMLOADEREXCEPTIONMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.problemLoaderExceptionMarker";
   public final static String RECURSIONMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.cycleDetectedMarker";
   public final static String OLDPROOFMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.oldProofMarker";
   
   
   /**
    * Creates the {@link MarkerManager#CLOSEDMARKER_ID} or {@link MarkerManager#NOTCLOSEDMARKER_ID} for the given {@link ProofElement}.
    * @param pe - the {@link ProofElement to use.
    * @throws CoreException
    */
   public void setMarker(ProofElement pe) throws CoreException {
      LinkedHashSet<IMarker> oldMarker = pe.getMarker();
      for(IMarker marker : oldMarker){
         if(marker != null){
            pe.removeMarker(marker);
            marker.delete();
         }
      }
      pe.setMarker(new LinkedHashSet<IMarker>());
      SourceLocation scl = pe.getSourceLocation();
      if(scl != null){
         if (pe.getProofClosed()) {
            IMarker marker = pe.getJavaFile().createMarker(CLOSEDMARKER_ID);
            if (marker.exists()) {
               marker.setAttribute(IMarker.MESSAGE, pe.getMarkerMsg());
               marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_INFO);
               marker.setAttribute(IMarker.LINE_NUMBER, scl.getLineNumber()); // Required for compatibility with other tools like FeatureIDE even if char start and end is defined.
               marker.setAttribute(IMarker.LOCATION, "line " + scl.getLineNumber()); // Otherwise value "Unknown" is shown in Problems-View
               marker.setAttribute(IMarker.CHAR_START, scl.getCharStart());
               marker.setAttribute(IMarker.CHAR_END, scl.getCharEnd());
               marker.setAttribute(IMarker.SOURCE_ID, pe.getProofFile().getFullPath().toString());
               pe.addMarker(marker);
            }
         }
         else {
            IMarker marker = pe.getJavaFile().createMarker(NOTCLOSEDMARKER_ID);
            if (marker.exists()) {
               marker.setAttribute(IMarker.MESSAGE, pe.getMarkerMsg());
               marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
               marker.setAttribute(IMarker.LINE_NUMBER, scl.getLineNumber()); // Required for compatibility with other tools like FeatureIDE even if char start and end is defined.
               marker.setAttribute(IMarker.LOCATION, "line " + scl.getLineNumber()); // Otherwise value "Unknown" is shown in Problems-View
               marker.setAttribute(IMarker.CHAR_START, scl.getCharStart());
               marker.setAttribute(IMarker.CHAR_END, scl.getCharEnd());
               marker.setAttribute(IMarker.SOURCE_ID, pe.getProofFile().getFullPath().toString());
               pe.addMarker(marker);
            }
         }
      }
   }
   
   
   /**
    * Creates the {@link MarkerManager#RECURSIONMARKER_ID} for the given {@ink ProofElement}.
    * @param pe - the {@link ProofElement} to use
    * @throws CoreException
    */
   public void setRecursionMarker(LinkedList<ProofElement> cycle) throws CoreException{
      ProofElement pe = cycle.get(0);
      LinkedHashSet<IMarker> oldMarker = pe.getMarker();
      for(IMarker marker : oldMarker){
         if(marker != null && !RECURSIONMARKER_ID.equals(marker.getType()) && !OLDPROOFMARKER_ID.equals(marker.getType())){
            pe.removeMarker(marker);
            marker.delete();
         }
      }
      IMarker marker = pe.getJavaFile().createMarker(RECURSIONMARKER_ID);
      if (marker.exists()) {
         marker.setAttribute(IMarker.MESSAGE, generateCycleDetectedMarkerMessage(cycle));
         marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
         marker.setAttribute(IMarker.LINE_NUMBER, pe.getSourceLocation().getLineNumber()); // Required for compatibility with other tools like FeatureIDE even if char start and end is defined.
         marker.setAttribute(IMarker.LOCATION, "line " + pe.getSourceLocation().getLineNumber()); // Otherwise value "Unknown" is shown in Problems-View
         marker.setAttribute(IMarker.CHAR_START, pe.getSourceLocation().getCharStart());
         marker.setAttribute(IMarker.CHAR_END, pe.getSourceLocation().getCharEnd());
         marker.setAttribute(IMarker.SOURCE_ID, pe.getProofFile().getFullPath().toString());
         pe.addMarker(marker);
      }
   }
   
   
   /** 
    * Generates the message for the cyclemarker of the given cycle,
    * @param cycle - the cycle to use
    * @return the marker message
    */
   private String generateCycleDetectedMarkerMessage(LinkedList<ProofElement> cycle){
      StringBuffer sb = new StringBuffer();
      sb.append("Cycle detected:");
      for(ProofElement pe : cycle){
         sb.append(StringUtil.NEW_LINE);
         sb.append(pe.getContract().getName());
      }
      return sb.toString();
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
    * Searches the {@link IMarker} for the given {@link ProofElement}.
    * @param scl - the {@link ProofElement} to use
    * @return the {@link IMarker} if found. null otherwise
    * @throws CoreException
    */
   public LinkedHashSet<IMarker> getOldProofMarker(IFile javaFile, SourceLocation scl, IFile proofFile) throws CoreException{
      LinkedHashSet<IMarker> oldMarker = new LinkedHashSet<IMarker>();
      LinkedList<IMarker> allFileKeYMarker = getAllkeYMarkerForScl(javaFile, scl);
      for(IMarker marker : allFileKeYMarker){
         String source = marker.getAttribute(IMarker.SOURCE_ID, "");
         if(source.equals(proofFile.getFullPath().toString())){
            oldMarker.add(marker);
         }
//         if(CLOSEDMARKER_ID.equals(marker.getType())){
//            if(message.equals("Proof closed: " + proofFile.getFullPath())){
//               oldMarker.add(marker);
//            }
//         }
//         else if(NOTCLOSEDMARKER_ID.equals(marker.getType())){
//            if(message.equals("Proof not closed: " + proofFile.getFullPath())){
//               oldMarker.add(marker);
//            }
//         }
//         else if(RECURSIONMARKER_ID.equals(marker.getType())){
//            if(message.startsWith("Cycle detected:" + StringUtil.NEW_LINE + proofFile.getFullPath())){
//               oldMarker.add(marker);
//            }
//         }
//         else if(OLDPROOFMARKER_ID.equals(marker.getType())){
//            if(message.equals("Outdated proof: " + proofFile.getFullPath())){
//               oldMarker.add(marker);
//            }
//         }
      }
      return oldMarker;
   }
   
   
   /**
    * Returns all {@link IMarker} for the given {@link SourceLocation}.
    * @param res - the {@link IResource} to use
    * @param scl - the {@link SourceLocation} to use
    * @return all {@link IMarker} for the {@link SourceLocation}
    * @throws CoreException
    */
   private LinkedList<IMarker> getAllkeYMarkerForScl(IResource res, SourceLocation scl) throws CoreException{
      LinkedList<IMarker> newMarkerList = new LinkedList<IMarker>();
      LinkedList<IMarker> markerList = getAllKeYMarker(res, IResource.DEPTH_ZERO);
      for(IMarker marker : markerList){
         Integer startChar = (Integer) marker.getAttribute(IMarker.CHAR_START);
         Integer endChar = (Integer) marker.getAttribute(IMarker.CHAR_END);
         if(scl.getCharStart() == startChar && scl.getCharEnd() == endChar){
            newMarkerList.add(marker);
         }
      }
      return newMarkerList;
   }
   
   
   /**
    * Collects all KeY{@link IMarker} for the given {@link IResource}.
    * @param res - the {@link IResource} to use
    * @return a {@link LinkedList} with all KeY{@link IMarker}
    * @throws CoreException
    */
   public LinkedList<IMarker> getAllKeYMarker(IResource res, int depth) throws CoreException{
      return getKeYMarkerByType(res, depth, CLOSEDMARKER_ID, NOTCLOSEDMARKER_ID, PROBLEMLOADEREXCEPTIONMARKER_ID, RECURSIONMARKER_ID, OLDPROOFMARKER_ID);
   }
   
   
   /**
    * Returns all {@link IMarker} matching the given types for the given {@link IResource}.
    * @param res - the {@link IResource} to use
    * @param depth - the depth to use
    * @param types - the types to look for
    * @return a {@link LinkedList} with all matching {@link IMarker}
    * @throws CoreException
    */
   public LinkedList<IMarker> getKeYMarkerByType(IResource res, int depth, String... types) throws CoreException{
      LinkedList<IMarker> markerList = new LinkedList<IMarker>();
      for(String type : types){
         if(CLOSEDMARKER_ID.equals(type) || NOTCLOSEDMARKER_ID.equals(type) || PROBLEMLOADEREXCEPTIONMARKER_ID.equals(type) || RECURSIONMARKER_ID.equals(type) || OLDPROOFMARKER_ID.equals(type)){
            markerList.addAll(markerArrayToList(res.findMarkers(type, true, depth)));
         }
      }
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
   
   
   public void deleteAllKeYMarker(IResource res, int depth) throws CoreException{
      deleteKeYMarkerByType(res, depth, CLOSEDMARKER_ID, NOTCLOSEDMARKER_ID, PROBLEMLOADEREXCEPTIONMARKER_ID, RECURSIONMARKER_ID, OLDPROOFMARKER_ID);
   }
   
   
   /**
    * Removes all KeYResource {@link IMarker} from the given {@link IResource} matching the given types using the given depth.
    * @param res - the {@link IResource} to use
    * @param type - the type to be delete
    * @param depth - the depth to use
    * @throws CoreException
    */
   public void deleteKeYMarkerByType(IResource res, int depth, String... types) throws CoreException{
      for(String type : types){
         if(CLOSEDMARKER_ID.equals(type)){
            res.deleteMarkers(CLOSEDMARKER_ID, true, depth);
         } else if(NOTCLOSEDMARKER_ID.equals(type)){
            res.deleteMarkers(NOTCLOSEDMARKER_ID, true, depth);
         } else if(PROBLEMLOADEREXCEPTIONMARKER_ID.equals(type)){
            res.deleteMarkers(PROBLEMLOADEREXCEPTIONMARKER_ID, true, depth);
         } else if(RECURSIONMARKER_ID.equals(type)){
            res.deleteMarkers(RECURSIONMARKER_ID, true, depth);
         }
      }
   }
}