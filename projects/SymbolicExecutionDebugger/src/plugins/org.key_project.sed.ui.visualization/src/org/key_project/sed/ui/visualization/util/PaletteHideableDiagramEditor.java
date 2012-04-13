package org.key_project.sed.ui.visualization.util;

import org.eclipse.gef.commands.CommandStack;
import org.eclipse.gef.ui.palette.FlyoutPaletteComposite.FlyoutPreferences;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeature;
import org.eclipse.graphiti.features.context.IContext;
import org.eclipse.graphiti.internal.command.CommandContainer;
import org.eclipse.graphiti.internal.command.GenericFeatureCommandWithContext;
import org.eclipse.graphiti.internal.command.ICommand;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.eclipse.graphiti.ui.internal.command.GefCommandWrapper;

/**
 * <p>
 * Extended {@link DiagramEditor} which allows to hide the palette.
 * </p>
 * <p>
 * This class allows also to execute {@link IFeature} and Graphiti {@link ICommand}
 * instances via {@link #executeFeature(IFeature, IContext)} and
 * {@link #executeCommand(ICommand)}.
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class PaletteHideableDiagramEditor extends DiagramEditor {
   /**
    * Defines if the palette is hidden or not.
    */
   private boolean paletteHidden;

   /**
    * Executes the given {@link IFeature} with the given {@link IContext}.
    * @param feature The {@link IFeature} to execute.
    * @param context the {@link IContext} to use.
    */
   public void executeFeature(IFeature feature, IContext context) {
      CommandContainer commandContainer = new CommandContainer(feature.getFeatureProvider());
      commandContainer.add(new GenericFeatureCommandWithContext(feature, context));
      executeCommand(commandContainer);
   }
   
   /**
    * Executes the given {@link ICommand} on the editing domain.
    * @param command The {@link ICommand} to execute.
    */
   protected void executeCommand(ICommand command) {
      CommandStack commandStack = getEditDomain().getCommandStack();
      commandStack.execute(new GefCommandWrapper(command, getEditingDomain()));
   }   
   
   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Overwritten to ignore warnings.
    * </p>
    */
   @Override
   public IDiagramTypeProvider getDiagramTypeProvider() {
      return super.getDiagramTypeProvider();
   }
   
   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Overwritten to ignore warnings.
    * </p>
    */
   @Override
   public void selectPictogramElements(PictogramElement[] pictogramElements) {
      super.selectPictogramElements(pictogramElements);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Overwritten to ignore warnings.
    * </p>
    */
   @Override
   public void refreshContent() {
      super.refreshContent();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Overwritten to ignore warnings.
    * </p>
    */
   @Override
   public PictogramElement[] getSelectedPictogramElements() {
      return super.getSelectedPictogramElements();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected FlyoutPreferences getPalettePreferences() {
      final FlyoutPreferences superPreferences = super.getPalettePreferences(); // Modification of this preferences is not possible, because the changes are shared with real editors
      if (isPaletteHidden()) {
         // Disable the palette: see http://www.eclipse.org/forums/index.php/t/263112/
         return new FlyoutPreferences() {
            @Override
            public int getDockLocation() {
               return superPreferences.getDockLocation();
            }

            @Override
            public int getPaletteState() {
               return 8; // org.eclipse.gef.ui.palette.FlyoutPaletteComposite.STATE_HIDDEN
            }

            @Override
            public int getPaletteWidth() {
               return superPreferences.getPaletteWidth();
            }

            @Override
            public void setDockLocation(int location) {
               superPreferences.setDockLocation(location);
            }

            @Override
            public void setPaletteState(int state) {
               superPreferences.setPaletteState(state);
            }

            @Override
            public void setPaletteWidth(int width) {
               superPreferences.setPaletteWidth(width);
            }
         };
      }
      else {
         return superPreferences;
      }
   }
   
   /**
    * Checks if the palette is hidden or not.
    * @return {@code true} palette is hidden, {@code false} palette is visible.
    */
   protected boolean isPaletteHidden() {
      return paletteHidden;
   }
   
   /**
    * Defines if the palette is hidden or not.
    * @param paletteHidden {@code true} palette is hidden, {@code false} palette is visible.
    */
   public void setPaletteHidden(boolean paletteHidden) {
      this.paletteHidden = paletteHidden;
   }
}
