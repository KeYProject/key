package org.key_project.key4eclipse.common.ui.test.starter;

import org.eclipse.core.resources.IProject;
import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.key4eclipse.common.ui.starter.IProjectStarter;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;

/**
 * {@link IGlobalStarter} which logs the calls of {@link #open(IProject)}.
 * @author Martin Hentschel
 */
public class FirstLoggingProjectStarter implements IProjectStarter, ITestedStarter {
   /**
    * The unique ID of this starter.
    */
   public static final String ID = "org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingProjectStarterID";

   /**
    * The unique Name of this starter.
    */
   public static final String NAME = "First Project Starter";

   /**
    * The description of this starter.
    */
   public static final String DESCRIPTION = "Description of First Project Starter";

   /**
    * The logged calls.
    */
   private ImmutableList<IProject> log = ImmutableSLList.nil();

   /**
    * {@inheritDoc}
    */
   @Override
   public void open(IProject project) throws Exception {
      log = log.append(project);
   }
   
   /**
    * Returns the logged calls and clears it.
    * @return The logged calls.
    */
   public ImmutableList<IProject> getAndResetLog() {
      ImmutableList<IProject> result = log;
      log = ImmutableSLList.nil();
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getId() {
      return ID;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return NAME;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return DESCRIPTION;
   }
}
