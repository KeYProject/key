package de.hentschel.visualdbc.interactive.proving.ui.job.event;

import java.util.EventObject;

import de.hentschel.visualdbc.interactive.proving.ui.job.StartProofJob;

/**
 * An event thrown from a {@link StartProofJob} and observed via
 * {@link IStartProofJobListener}.
 * @author Martin Hentschel
 */
public class StartProofJobEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -2591196704008024760L;

   /**
    * Constructor.
    * @param source The {@link StartProofJob} that has thrown this event.
    */
   public StartProofJobEvent(StartProofJob source) {
      super(source);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public StartProofJob getSource() {
      return (StartProofJob)super.getSource();
   }
}
