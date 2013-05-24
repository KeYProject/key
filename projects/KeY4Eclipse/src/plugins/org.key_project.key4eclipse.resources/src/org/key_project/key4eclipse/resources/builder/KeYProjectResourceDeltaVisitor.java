package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedList;

import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;

public class KeYProjectResourceDeltaVisitor implements IResourceDeltaVisitor{

   private LinkedList<IResourceDelta> deltas;
   public KeYProjectResourceDeltaVisitor() throws CoreException{
      this.deltas = new LinkedList<IResourceDelta>();
   }
   
   
   public LinkedList<IResourceDelta> getDeltaList(){
      return this.deltas;
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(IResourceDelta delta) throws CoreException {
      deltas.add(delta);

      return true;
   }
   
   

}
