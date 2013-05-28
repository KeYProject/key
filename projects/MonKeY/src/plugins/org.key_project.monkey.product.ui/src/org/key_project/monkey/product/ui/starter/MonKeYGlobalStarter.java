package org.key_project.monkey.product.ui.starter;

import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.monkey.product.ui.perspective.MonKeYPerspective;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Starts MonKeY which means that the MonKeY perspective is opened.
 * @author Martin Hentschel
 */
public class MonKeYGlobalStarter implements IGlobalStarter {
   /**
    * {@inheritDoc}
    */
   @Override
   public void open() throws Exception {
      WorkbenchUtil.openPerspective(MonKeYPerspective.ID);
   }
}
