package org.key_project.sed.ui.slicing.event;

import java.util.EventListener;

import org.key_project.sed.ui.slicing.SlicingSettingsControl;

/**
 * Listens for changes on a {@link SlicingSettingsControl}.
 * @author Martin Hentschel
 */
public interface ISlicingSettingsControlListener extends EventListener {
   /**
    * When the selected settings have changed.
    * @param e The {@link SlicingSettingsControlEvent}.
    */
   public void settingsChanged(SlicingSettingsControlEvent e);
}
