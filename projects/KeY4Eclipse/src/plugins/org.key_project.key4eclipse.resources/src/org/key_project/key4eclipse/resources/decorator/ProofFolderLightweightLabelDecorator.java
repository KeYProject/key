package org.key_project.key4eclipse.resources.decorator;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.BaseLabelProvider;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.key_project.key4eclipse.resources.Activator;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

/**
 * Decorates the proof folder of KeY projects.
 * @author Martin Hentschel
 */
public class ProofFolderLightweightLabelDecorator extends BaseLabelProvider implements ILightweightLabelDecorator {
   /**
    * {@inheritDoc}
    */
   @Override
   public void decorate(Object element, IDecoration decoration) {
      try {
         if (element instanceof IFolder && KeYResourcesUtil.isProofFolder((IFolder)element)) {
            decoration.addOverlay(Activator.imageDescriptorFromPlugin(Activator.PLUGIN_ID, "icons/projectIcon.png"));
         }
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
      }
   }
}
