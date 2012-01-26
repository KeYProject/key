package de.hentschel.visualdbc.interactive.proving.ui.job.event;

import java.util.EventListener;

import de.hentschel.visualdbc.interactive.proving.ui.job.StartProofJob;

/**
 * Observes events on {@link StartProofJob}s.
 * @author Martin Hentschel
 */
public interface IStartProofJobListener extends EventListener {
   /**
    * When a job {@link StartProofJob} has finished.
    * @param e The event.
    */
   public void jobFinished(StartProofJobEvent e);
}
