package de.hentschel.visualdbc.interactive.proving.ui.util.event;

import java.util.EventListener;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveConnectionUtil;

/**
 * Observes changes of {@link InteractiveConnectionUtil}.
 * @author Martin Hentschel
 */
public interface IInteractiveConnectionUtilListener extends EventListener {
   /**
    * When a new {@link IDSConnection} was opened.
    * @param e The event.
    */
   public void connectionOpened(InteractiveConnectionUtilEvent e);
}
