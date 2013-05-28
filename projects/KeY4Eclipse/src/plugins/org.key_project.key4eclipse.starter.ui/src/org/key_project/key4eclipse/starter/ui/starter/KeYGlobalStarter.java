package org.key_project.key4eclipse.starter.ui.starter;

import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

/**
 * Starts the original user interface of KeY.
 * @author Martin Hentschel
 */
public class KeYGlobalStarter implements IGlobalStarter {
   /**
    * {@inheritDoc}
    */
   @Override
   public void open() throws Exception {
      KeYUtil.openMainWindowAsync();
   }
}
