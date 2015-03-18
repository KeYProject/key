package org.key_project.key4eclipse.starter.core.decorator;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.BaseLabelProvider;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.key_project.key4eclipse.starter.core.Activator;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry.KeYClassPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.key4eclipse.starter.core.util.LogUtil;

/**
 * Provides the basic functionality to decorate class path {@link IResource}s.
 * @author Martin Hentschel
 */
public abstract class AbstractClassPathLightweightLabelDecorator extends BaseLabelProvider implements ILightweightLabelDecorator {
   /**
    * {@inheritDoc}
    */
   @Override
   public void decorate(Object element, IDecoration decoration) {
      try {
         if (element instanceof IResource) {
            IResource resource = (IResource) element;
            String resourcePath = resource.getFullPath().toString();
            IProject project = resource.getProject();
            // Check boot class path
            if (UseBootClassPathKind.WORKSPACE.equals(KeYResourceProperties.getUseBootClassPathKind(project))) {
               String path = KeYResourceProperties.getBootClassPath(project);
               if (resourcePath.equals(path)) {
                  decoration.addOverlay(AbstractUIPlugin.imageDescriptorFromPlugin(Activator.PLUGIN_ID, getBootOverlay()));
                  return; // For efficiency
               }
            }
            // Check class path
            List<KeYClassPathEntry> entries = KeYResourceProperties.getClassPathEntries(project);
            KeYClassPathEntry entry = KeYResourceProperties.searchClassPathEntry(entries, KeYClassPathEntryKind.WORKSPACE, resourcePath);
            if (entry != null) {
               decoration.addOverlay(AbstractUIPlugin.imageDescriptorFromPlugin(Activator.PLUGIN_ID, getClassPathOverlay()));
            }
         }
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
      }
   }
   
   /**
    * Returns the path to the boot overlay image.
    * @return The path to the boot overlay image.
    */
   protected abstract String getBootOverlay();
   
   /**
    * Returns the path to the class path overlay image.
    * @return The path to the class path overlay image.
    */
   protected abstract String getClassPathOverlay();
   
   /**
    * Re-decorates the given element.
    * @param element The element to re-decorate.
    */
   public void redecorate(Object element) {
      fireLabelProviderChanged(new LabelProviderChangedEvent(this, element));
   }
}
