package org.key_project.key4eclipse.resources.builder;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

public class KeYProjectDeltaManager {

   private static KeYProjectDeltaManager instance;
   private Map<IProject, KeYProjectDelta> projectDeltas;
   
   private KeYProjectDeltaManager(){
      projectDeltas = Collections.synchronizedMap(new HashMap<IProject, KeYProjectDelta>());
   }
   
   public static synchronized KeYProjectDeltaManager getInstance(){
      if(instance == null){
         KeYProjectDeltaManager.instance = new KeYProjectDeltaManager();
      }
      return KeYProjectDeltaManager.instance;
   }
   
   public void update(IResourceDelta delta){
      IProject project = KeYResourcesUtil.getProject(delta);
      KeYProjectDeltaVisitor visitor = new KeYProjectDeltaVisitor(project);
      try{
         delta.accept(visitor);
         KeYProjectDelta keyDelta = getDelta(project);
         keyDelta.addChangedJavaFiles(visitor.getChangedJavaFiles());
         keyDelta.addChangedProofAndMetaFiles(visitor.getChangedProofAndMetaFiles());
      } catch (CoreException e){
         LogUtil.getLogger().logError(e);
      }
   }
   
   public KeYProjectDelta getDelta(IProject project){
      KeYProjectDelta keyDelta = projectDeltas.get(project);
      if(keyDelta == null){
         projectDeltas.put(project, new KeYProjectDelta());
         keyDelta = projectDeltas.get(project);
      }
      return keyDelta;
   }
}
