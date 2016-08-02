package org.key_project.sed.ui.slicing.event;

import java.util.EventObject;

import org.key_project.sed.ui.slicing.SlicingSettingsControl;

/**
 * An event thrown by a {@link SlicingSettingsControl} and observed
 * by an {@link ISlicingSettingsControlListener}.
 * @author Martin Hentschel
 */
public class SlicingSettingsControlEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 890753943043572769L;

   /**
    * Constructor.
    * @param source The source {@link SlicingSettingsControl}.
    */
   public SlicingSettingsControlEvent(SlicingSettingsControl source) {
      super(source);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SlicingSettingsControl getSource() {
      return (SlicingSettingsControl) super.getSource();
   }
}
