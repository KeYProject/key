package org.key_project.key4eclipse.resources.builder;

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

   
   public void setMarker(Proof proof, IMethod method) throws CoreException {
      // get File from Method
      IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
      IPath methodPath = method.getPath();
      IFile file = workspaceRoot.getFile(methodPath);
      
      // set marker
      if (proof.closed()) {
         IMarker marker = file.createMarker("org.key_project.key4eclipse.resources.ui.marker.proofClosedMarker");
         if (marker.exists()) {
            marker.setAttribute(IMarker.MESSAGE, "Proof closed");
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_INFO);
            marker.setAttribute(IMarker.LINE_NUMBER, getLineNumberOfMethod(method));
         }
      }
      else {
         IMarker marker = file.createMarker("org.key_project.key4eclipse.resources.ui.marker.proofNotClosedMarker");
         if (marker.exists()) {
            marker.setAttribute(IMarker.MESSAGE, "Proof not closed");
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
            marker.setAttribute(IMarker.LINE_NUMBER, getLineNumberOfMethod(method));
         }
      }
   }
   
   
   public void deleteMarkers(IResource res) throws CoreException{
      IMarker[] closedMarkers = res.findMarkers("org.key_project.key4eclipse.resources.ui.marker.proofClosedMarker", false, IResource.DEPTH_INFINITE); 
      for(IMarker marker : closedMarkers){
         marker.delete();
      }
      
      IMarker[] notClosedMarkers = res.findMarkers("org.key_project.key4eclipse.resources.ui.marker.proofNotClosedMarker", false, IResource.DEPTH_INFINITE);
      for(IMarker marker : notClosedMarkers){
         marker.delete();
      }
   }
   
   public void deleteMarkers(IMethod method) throws CoreException{
      int line = getLineNumberOfMethod(method);
      IMarker[] closedMarkers = method.getResource().findMarkers("org.key_project.key4eclipse.resources.ui.marker.proofClosedMarker", false, IResource.DEPTH_INFINITE); 
      for(IMarker marker : closedMarkers){
         if(marker.getAttribute(IMarker.LINE_NUMBER, -1) == line){
            marker.delete();
         } 
      }
      
      IMarker[] notClosedMarkers = method.getResource().findMarkers("org.key_project.key4eclipse.resources.ui.marker.proofNotClosedMarker", false, IResource.DEPTH_INFINITE);
      for(IMarker marker : notClosedMarkers){
         if(marker.getAttribute(IMarker.LINE_NUMBER, -1) == line){
            marker.delete();
         }
      }
   }
   
   
   private int getLineNumberOfMethod(IMethod method)
         throws CoreException {
      Position pos = KeYUtil.getCursorPositionForOffset(method, method.getNameRange().getOffset());
      return pos.getLine();
   }
}
