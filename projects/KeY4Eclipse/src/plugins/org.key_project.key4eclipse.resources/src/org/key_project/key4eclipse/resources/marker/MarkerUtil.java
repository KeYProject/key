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

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;

/**
 * Provides methods to create and delete all KeY{@link IMarker}.
 * @author Stefan Käsdorf
 */
public class MarkerUtil {
   
   public final static String CLOSEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.proofClosedMarker";
   public final static String NOTCLOSEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.proofNotClosedMarker";
   public final static String PROBLEMLOADEREXCEPTIONMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.problemLoaderExceptionMarker";
   public final static String RECURSIONMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.cycleDetectedMarker";
   public final static String MARKER_ATTRIBUTE_OUTDATED = "org.key_project.key4eclipse.resources.ui.marker.attribute.outdated";
   
   public final static String TYPE = "org.key_project.key4eclipse.resources.ui.marker.attribute.type";
   public final static String METHOD_NAME = "org.key_project.key4eclipse.resources.ui.marker.attribute.methodName";
   public final static String METHOD_PARAMETERS = "org.key_project.key4eclipse.resources.ui.marker.attribute.methodParameters";
   
   /**
    * Creates the {@link MarkerUtil#CLOSEDMARKER_ID} or {@link MarkerUtil#NOTCLOSEDMARKER_ID} for the given {@link ProofElement}.
    * @param pe - the {@link ProofElement to use.
    * @throws CoreException
    */
   public static void setMarker(ProofElement pe) {

      try{
         IMarker proofMarker = pe.getProofMarker();
         if(proofMarker != null){
            proofMarker.delete();
         }
         pe.setProofMarker(null);
         SourceLocation scl = pe.getSourceLocation();
         if(scl != null){
            IMarker marker = null;
            if (pe.getProofClosed()) {
               marker = pe.getJavaFile().createMarker(CLOSEDMARKER_ID);
               if (marker.exists()) {
                  marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_INFO);
               }
            }
            else {
               marker = pe.getJavaFile().createMarker(NOTCLOSEDMARKER_ID);
               if (marker.exists()) {
                  marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
               }
            }
            marker.setAttribute(IMarker.MESSAGE, pe.getMarkerMsg());
            marker.setAttribute(IMarker.LINE_NUMBER, scl.getLineNumber()); // Required for compatibility with other tools like FeatureIDE even if char start and end is defined.
            marker.setAttribute(IMarker.LOCATION, "line " + scl.getLineNumber()); // Otherwise value "Unknown" is shown in Problems-View
            marker.setAttribute(IMarker.CHAR_START, scl.getCharStart());
            marker.setAttribute(IMarker.CHAR_END, scl.getCharEnd());
            marker.setAttribute(IMarker.SOURCE_ID, pe.getProofFile().getFullPath().toString());
            marker.setAttribute(MarkerUtil.MARKER_ATTRIBUTE_OUTDATED, pe.getOutdated());
            
            // Try to save method information which makes debugging a proof with SED easier.
            if (pe.getContract() != null) {
               IObserverFunction target = pe.getContract().getTarget();
               if (target instanceof IProgramMethod) {
                  IProgramMethod pm = (IProgramMethod) target;
                  KeYJavaType type = pe.getContract().getKJT();
                  String[] parameterTypes = new String[pm.getParameters().size()];
                  for (int i = 0; i < parameterTypes.length; i++) {
                     parameterTypes[i] = pm.getParameters().get(i).getTypeReference().getKeYJavaType().getFullName();
                  }               
                  marker.setAttribute(MarkerUtil.TYPE, type.getFullName());
                  marker.setAttribute(MarkerUtil.METHOD_NAME, pm.getName());
                  marker.setAttribute(MarkerUtil.METHOD_PARAMETERS, ArrayUtil.toString(parameterTypes, ";"));
               }
            }
            
            pe.setProofMarker(marker);
         }
      } catch(CoreException e){
         LogUtil.getLogger().logError(e);
      }
   }
   
   
   /**
    * Creates the {@link MarkerUtil#RECURSIONMARKER_ID} for the given {@ink ProofElement}.
    * @param pe - the {@link ProofElement} to use
    * @throws CoreException
    */
   public static void setRecursionMarker(List<ProofElement> cycle) {
      try{
         ProofElement pe = cycle.get(0);
         IMarker proofMarker = pe.getProofMarker();
         if(proofMarker != null){
            proofMarker.delete();
         }
         pe.setProofMarker(null);
   
         IMarker marker = pe.getJavaFile().createMarker(RECURSIONMARKER_ID);
         if (marker.exists()) {
            marker.setAttribute(IMarker.MESSAGE, generateCycleDetectedMarkerMessage(cycle));
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
            marker.setAttribute(IMarker.LINE_NUMBER, pe.getSourceLocation().getLineNumber()); // Required for compatibility with other tools like FeatureIDE even if char start and end is defined.
            marker.setAttribute(IMarker.LOCATION, "line " + pe.getSourceLocation().getLineNumber()); // Otherwise value "Unknown" is shown in Problems-View
            marker.setAttribute(IMarker.CHAR_START, pe.getSourceLocation().getCharStart());
            marker.setAttribute(IMarker.CHAR_END, pe.getSourceLocation().getCharEnd());
            marker.setAttribute(IMarker.SOURCE_ID, pe.getProofFile().getFullPath().toString());
            marker.setAttribute(MarkerUtil.MARKER_ATTRIBUTE_OUTDATED, pe.getOutdated());
            pe.addRecursionMarker(marker);
         }
      }
      catch(CoreException e){
         LogUtil.getLogger().logError(e);
      }
   }
   
   
   public static void setOutdated(ProofElement pe, boolean outdated){
      IMarker proofMarker = pe.getProofMarker();
      List<IMarker> recursionMarker = pe.getRecursionMarker();
      if(proofMarker != null && proofMarker.exists()){
         try {
            String msg = getUpdatedOutdatedProofMessage(proofMarker.getAttribute(IMarker.MESSAGE, ""), outdated);
            pe.setMarkerMsg(msg);            
            proofMarker.setAttribute(MarkerUtil.MARKER_ATTRIBUTE_OUTDATED, outdated);
            proofMarker.setAttribute(IMarker.MESSAGE, msg);
         }
         catch (CoreException e) {
            LogUtil.getLogger().logError(e);
         }
      }
      else {
         for(IMarker marker : recursionMarker){
            if(marker != null && marker.exists()){
               try {
                  String msg = getUpdatedOutdatedProofMessage(marker.getAttribute(IMarker.MESSAGE, ""), outdated);
                  marker.setAttribute(MarkerUtil.MARKER_ATTRIBUTE_OUTDATED, outdated);
                  marker.setAttribute(IMarker.MESSAGE, msg);
               }
               catch (CoreException e) {
                  LogUtil.getLogger().logError(e);
               }
            }
         }
      }
   }
         
      
   private static String getUpdatedOutdatedProofMessage(String message, boolean outdated) {
      String appendix = StringUtil.NEW_LINE + StringUtil.NEW_LINE + "Outdated proof - new build required!";
      StringBuilder sb = new StringBuilder(message);
      
      int appendixIndex = sb.indexOf(appendix);
      if(appendixIndex != -1){
         sb.delete(appendixIndex, sb.length()-1);
      }
      
      if(outdated){
         sb.append(appendix);
      }
      return sb.toString();
   }
   
   
   /** 
    * Generates the message for the recursion{@link IMarker} of the given cycle,
    * @param cycle - the cycle to use
    * @return the marker message
    */
   private static String generateCycleDetectedMarkerMessage(List<ProofElement> cycle){
      StringBuffer sb = new StringBuffer();
      sb.append("Cycle detected:");
      for(ProofElement pe : cycle){
         sb.append(StringUtil.NEW_LINE);
         sb.append(pe.getContract().getName());
      }
         sb = new StringBuffer(getUpdatedOutdatedProofMessage(sb.toString(), cycle.get(0).getOutdated()));
      return sb.toString();
   }
      
   
   /**
    * Creates the ProofLoaderException{@link IMarker} for the given {@link IResource}.
    * @param res - the {@link IResource} to use
    * @throws CoreException
    */
   public static void setProblemLoaderExceptionMarker(IResource res, int lineNumber, String msg) throws CoreException{
      deleteKeYMarkerByType(res.getProject(), IResource.DEPTH_INFINITE, MarkerUtil.PROBLEMLOADEREXCEPTIONMARKER_ID);
      IMarker marker = res.createMarker(PROBLEMLOADEREXCEPTIONMARKER_ID);
      if (marker.exists()) {
         marker.setAttribute(IMarker.MESSAGE, msg);
         marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
         if(res instanceof IFile && lineNumber != -1){
            marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
         }
      }
   }
   
   
   public static IMarker getProofMarker(IFile javaFile, SourceLocation scl, IFile proofFile){
      IMarker proofMarker = null;
      List<IMarker> markerList = null;
      markerList = getKeYMarkerByType(javaFile, IResource.DEPTH_ZERO, CLOSEDMARKER_ID, NOTCLOSEDMARKER_ID);
      for(IMarker marker : markerList){
         if(marker != null && marker.exists()){
            try{
               Integer startChar = (Integer) marker.getAttribute(IMarker.CHAR_START);
               Integer endChar = (Integer) marker.getAttribute(IMarker.CHAR_END);
               String source = marker.getAttribute(IMarker.SOURCE_ID, null);
               if(startChar != null && scl.getCharStart() == startChar 
                  && endChar != null && scl.getCharEnd() == endChar 
                  && source != null && source.equals(proofFile.getFullPath().toString())){
                  proofMarker = marker;
                  break;
               }
            } catch(CoreException e){
               LogUtil.getLogger().logError(e);
            }
         }
      }
      return proofMarker;
   }
   
   
   public static List<IMarker> getRecursionMarker(IFile javaFile, SourceLocation scl, IFile proofFile){
      List<IMarker> recursionMarker = new LinkedList<IMarker>();
      List<IMarker> markerList = null;
      markerList = getKeYMarkerByType(javaFile, IResource.DEPTH_ZERO, RECURSIONMARKER_ID);
      for(IMarker marker : markerList){
         if(marker != null && marker.exists()){
            try{
               Integer startChar = (Integer) marker.getAttribute(IMarker.CHAR_START);
               Integer endChar = (Integer) marker.getAttribute(IMarker.CHAR_END);
               String source = marker.getAttribute(IMarker.SOURCE_ID, null);
               if(scl.getCharStart() == startChar && scl.getCharEnd() == endChar && source != null && source.equals(proofFile.getFullPath().toString())){
                  recursionMarker.add(marker);
               }
            } catch (CoreException e) {
               return new LinkedList<IMarker>();
            }
         }
      }
      return recursionMarker;
   }


   /**
    * Collects all KeY{@link IMarker} for the given {@link IResource}.
    * @param res - the {@link IResource} to use
    * @return a {@link LinkedList} with all KeY{@link IMarker}
    * @throws CoreException
    */
   public static LinkedList<IMarker> getAllKeYMarker(IResource res, int depth) {
      return getKeYMarkerByType(res, depth, CLOSEDMARKER_ID, NOTCLOSEDMARKER_ID, PROBLEMLOADEREXCEPTIONMARKER_ID, RECURSIONMARKER_ID);
   }
   
   
   /**
    * Returns all {@link IMarker} matching the given types for the given {@link IResource}.
    * @param res - the {@link IResource} to use
    * @param depth - the depth to use
    * @param types - the types to look for
    * @return a {@link LinkedList} with all matching {@link IMarker}
    * @throws CoreException
    */
   public static LinkedList<IMarker> getKeYMarkerByType(IResource res, int depth, String... types){
      LinkedList<IMarker> markerList = new LinkedList<IMarker>();
      for(String type : types){
         if(CLOSEDMARKER_ID.equals(type) || NOTCLOSEDMARKER_ID.equals(type) || PROBLEMLOADEREXCEPTIONMARKER_ID.equals(type) || RECURSIONMARKER_ID.equals(type)){
            try {
               markerList.addAll(KeYResourcesUtil.arrayToList(res.findMarkers(type, true, depth)));
            }
            catch (CoreException e) {
               LogUtil.getLogger().logError(e);
            }
         }
      }
      return markerList;
   }
   
   
   /**
    * Removes all KeYResource {@link IMarker} from the given {@link IResource} matching the given types using the given depth.
    * @param res - the {@link IResource} to use
    * @param type - the type to be delete
    * @param depth - the depth to use
    * @throws CoreException
    */
   public static void deleteKeYMarkerByType(IResource res, int depth, String... types) throws CoreException{
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
