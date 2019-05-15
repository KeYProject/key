package de.uka.ilkd.key.control.event;

import java.util.EventObject;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;

/**
 * An event thrown by a {@link TermLabelVisibilityManager}.
 * @author Martin Hentschel
 */
public class TermLabelVisibilityManagerEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 2827200355462914026L;

   /**
    * Constructor.
    * @param source The source {@link TermLabelVisibilityManager}.
    */
   public TermLabelVisibilityManagerEvent(TermLabelVisibilityManager source) {
      super(source);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public TermLabelVisibilityManager getSource() {
      return (TermLabelVisibilityManager) super.getSource();
   }
}
