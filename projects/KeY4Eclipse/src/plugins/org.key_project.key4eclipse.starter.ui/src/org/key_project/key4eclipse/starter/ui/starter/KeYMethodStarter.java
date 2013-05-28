package org.key_project.key4eclipse.starter.ui.starter;

import org.eclipse.jdt.core.IMethod;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

/**
 * Starts a proof in the original user interface of KeY.
 * @author Martin Hentschel
 */
public class KeYMethodStarter implements IMethodStarter {
   /**
    * {@inheritDoc}
    */
   @Override
   public void open(IMethod method) throws Exception {
      KeYUtil.startProofAsync(method);
   }
}
