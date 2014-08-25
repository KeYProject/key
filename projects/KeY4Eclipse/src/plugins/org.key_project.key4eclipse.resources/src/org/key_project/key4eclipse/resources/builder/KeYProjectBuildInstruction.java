package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;

public class KeYProjectBuildInstruction {

   private IProject project;
   boolean clean;
   private List<Object> elementsToBuild;
   
   public KeYProjectBuildInstruction(IProject project, boolean clean){
      this.project = project;
      this.clean = clean;
      this.elementsToBuild = null;
   }
   
   public IProject getProject(){
      return project;
   }
   
   public boolean getClean(){
      return clean;
   }
      
   public List<Object> getElementsToBuild(){
      return elementsToBuild;
   }
   
   public void addElementToBuild(Object elementToBuild){
      if(this.elementsToBuild == null){
         this.elementsToBuild = new LinkedList<Object>();
      }
      this.elementsToBuild.add(elementToBuild);
   }
   
   public void addAllElementsToBuild(List<IFile> elementsToBuild){
      if(this.elementsToBuild == null){
         this.elementsToBuild = new LinkedList<Object>();
      }
      this.elementsToBuild.addAll(elementsToBuild);
   }
}
