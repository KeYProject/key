package org.key_project.key4eclipse.common.ui.test.starter;

import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;

/**
 * {@link IGlobalStarter} which logs the calls of {@link #open()}.
 * @author Martin Hentschel
 */
public class FirstLoggingGlobalStarter implements IGlobalStarter, ITestedStarter {
   /**
    * The unique ID of this starter.
    */
   public static final String ID = "org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingGlobalStarterID";

   /**
    * The unique Name of this starter.
    */
   public static final String NAME = "First Global Starter";

   /**
    * The description of this starter.
    */
   public static final String DESCRIPTION = "Description of First Global Starter";

   /**
    * The counted number of calls.
    */
   private int openCount = 0;

   /**
    * {@inheritDoc}
    */
   @Override
   public void open() throws Exception {
      openCount++;
   }
   
   /**
    * Returns the counted number of calls and resets it to zero.
    * @return The number of calls.
    */
   public int getAndResetOpenCount() {
      int result = openCount;
      openCount = 0;
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
