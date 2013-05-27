package org.key_project.key4eclipse.resources.marker;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IMethod;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.proof.Proof;

public class MarkerManager {
   
   public final static String CLOSEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.proofClosedMarker";
   public final static String NOTCLOSEDMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.proofNotClosedMarker";
   public final static String PROBLEMLOADEREXCEPTIONMARKER_ID = "org.key_project.key4eclipse.resources.ui.marker.problemLoaderExceptionMarker";
   
   
   /**
    * Sets the {@link IMarker} for the given {@link IMethod} depending on the {@link Proof}s status. The {@link IPath} of 
    * the given Proof-{@link IFile} will be stored in the {@link IMarker} as attribute.
    * @param proof - the {@link Proof} to use for isClosed() check
    * @param method - the {@link IMethod} to store the {@link IMarker at.
    * @param proofFile - the {@link IFile} to use for remembering the {@link IPath}
    * @throws CoreException
    */
   public void setMarker(Proof proof, IMethod method, IFile proofFile) throws CoreException {
      // get File from Method
      IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
      IPath methodPath = method.getPath();
      IFile file = workspaceRoot.getFile(methodPath);

      // set marker
      if (proof.closed()) {
         IMarker marker = file.createMarker(CLOSEDMARKER_ID);
         if (marker.exists()) {
            marker.setAttribute(IMarker.MESSAGE, "Proof closed: " + proof.name().toString());
            marker.setAttribute(IMarker.TEXT, proofFile.getFullPath());
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_INFO);
            marker.setAttribute(IMarker.LINE_NUMBER, getLineNumberOfMethod(method));
         }
      }
      else {
         IMarker marker = file.createMarker(NOTCLOSEDMARKER_ID);
         if (marker.exists()) {
            marker.setAttribute(IMarker.MESSAGE, "Proof not closed: " + proof.name().toString());
            marker.setAttribute(IMarker.TEXT, proofFile.getFullPath());
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
            marker.setAttribute(IMarker.LINE_NUMBER, getLineNumberOfMethod(method));
         }
      }
   }
   
   public void setMarkerForAltProofElement(Proof proof, int lineNumber, IFile javaFile, IFile proofFile) throws CoreException {

      // set marker
      if (proof.closed()) {
         IMarker marker = javaFile.createMarker(CLOSEDMARKER_ID);
         if (marker.exists()) {
            marker.setAttribute(IMarker.MESSAGE, "Proof closed: " + proof.name().toString());
            marker.setAttribute(IMarker.TEXT, proofFile.getFullPath());
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_INFO);
            marker.setAttribute(IMarker.LINE_NUMBER, lineNumber); // TODO: Add also start and end character use KeyUti#convertToSourceLocation() to convert a PositionInfo with tab size from KeY into position info with tab size from Eclipse
            // TODO: Find out how to make marker type persistent
         }
      }
      else {
         IMarker marker = javaFile.createMarker(NOTCLOSEDMARKER_ID);
         if (marker.exists()) {
            marker.setAttribute(IMarker.MESSAGE, "Proof not closed: " + proof.name().toString());
            marker.setAttribute(IMarker.TEXT, proofFile.getFullPath());
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
            marker.setAttribute(IMarker.LINE_NUMBER, lineNumber); // TODO: Add also start and end character use KeyUti#convertToSourceLocation() to convert a PositionInfo with tab size from KeY into position info with tab size from Eclipse
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
   
   
   /**
    * Returns the lineNumber of the given {@link IMethod}.
    * @param method - the {@link IMethod} to use
    * @return the lineNumber of the {@link IMethod}
    * @throws CoreException
    */
   private int getLineNumberOfMethod(IMethod method) throws CoreException {
      Position pos = KeYUtil.getCursorPositionForOffset(method, method.getNameRange().getOffset());
      return pos.getLine();
   }
}
