package de.hentschel.visualdbc.datasource.key.model.event;

import java.util.EventListener;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.model.KeyProof;

/**
 * Allows to observe changes on a {@link KeyConnection}.
 * @author Martin Hentschel
 */
public interface IKeYConnectionListener extends EventListener {
   /**
    * When an interactive {@link KeyProof} was started.
    * @param e The {@link KeYConnectionEvent}.
    */
   public void interactiveProofStarted(KeYConnectionEvent e);
}
