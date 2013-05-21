package org.key_project.key4eclipse.resources.builder;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.key4eclipse.resources.util.LogUtil;

public class KeYProjectBuilder extends IncrementalProjectBuilder {

   public final static String BUILDER_ID = "org.key_project.key4eclipse.resources.KeYProjectBuilder";
   
   private ProofManager proofManager;
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IResourceDelta delta = getDelta(getProject());
      if (delta != null) {
         proofManager = new ProofManager(getProject());
         //visit all deltas
         delta.accept(new KeYProjectResourceDeltaVisitor(proofManager));
      }
      return null;
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void clean(IProgressMonitor monitor) throws CoreException {
      try {
         proofManager = new ProofManager(getProject());
         proofManager.clean();
         super.clean(monitor);
      }
      catch (Exception e) {
         LogUtil.getLogger().createErrorStatus(e);
      }
      
   }
}
