package org.key_project.sed.ui.visualization.util;

import org.eclipse.gef.ui.palette.FlyoutPaletteComposite.FlyoutPreferences;
import org.eclipse.graphiti.ui.editor.DiagramEditor;

/**
 * Extended {@link DiagramEditor} which allows to hide the palette.
 * @author Martin Hentschel
 */
public class PaletteHideableDiagramEditor extends DiagramEditor {
   /**
    * Defines if the palette is hidden or not.
    */
   private boolean paletteHidden;

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
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
