package org.key_project.key4eclipse.resources.builder;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.key4eclipse.resources.util.LogUtil;

import de.uka.ilkd.key.proof.ProblemLoaderException;

public class KeYProjectBuilder extends IncrementalProjectBuilder {

   public final static String BUILDER_ID = "org.key_project.key4eclipse.resources.KeYProjectBuilder";
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IResourceDelta delta = getDelta(getProject());
      if (delta != null) {
         try {
            IProject project = delta.getResource().getProject();
            //visit all deltas
            delta.accept(new KeYProjectResourceDeltaVisitor(project));
         }
         catch (ProblemLoaderException e) {
            LogUtil.getLogger().createErrorStatus(e);
         }
      }
      return null;
   }
}
