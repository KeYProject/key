package org.key_project.keyide.ui.starter;

import org.eclipse.jdt.core.IMethod;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.keyide.ui.util.KeYIDEUtil;

/**
 * Starts a proof in the KeYIDE user interface integrated in Eclipse.
 * @author Martin Hentschel
 */
public class KeYIDEMethodStarter implements IMethodStarter {
   /**
    * The unique ID of this starter.
    */
   public static final String STARTER_ID = "org.key_project.keyide.ui.starter.KeYIDEMethodStarter";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void open(IMethod method) throws Exception {
      KeYIDEUtil.openProofEditor(method);
      KeYIDEUtil.switchPerspective();
   }
}
