package org.key_project.key4eclipse.resources.builder;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IProject;

/**
 * Manages the {@link KeYProjectDelta}, updates and creates them.
 * @author Stefan Käsdorf
 */
public class KeYProjectDeltaManager {

   private static KeYProjectDeltaManager instance;
   private Map<IProject, KeYProjectDelta> projectDeltas;
   
   private KeYProjectDeltaManager(){
      projectDeltas = Collections.synchronizedMap(new HashMap<IProject, KeYProjectDelta>());
   }
   
   /**
    * Returns the static instance of the {@link KeYProjectDeltaManager}
    * @return the {@link KeYProjectDeltaManager} instance to use
    */
   public static synchronized KeYProjectDeltaManager getInstance(){
      if(instance == null){
         KeYProjectDeltaManager.instance = new KeYProjectDeltaManager();
      }
      return KeYProjectDeltaManager.instance;
   }
   
   /**
    * Returns the {@link KeYProjectDelta} for the given {@link IProject}. If there is no {@link KeYProjectDelta} yet, a new one will be created.
    * @param project
    * @return
    */
   public KeYProjectDelta getDelta(IProject project){
      synchronized(projectDeltas){
         KeYProjectDelta keyDelta = projectDeltas.get(project);
         if(keyDelta == null){
            keyDelta = new KeYProjectDelta(project);
            projectDeltas.put(project, keyDelta);
         }
         return keyDelta;
      }
   }
}
