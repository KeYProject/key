package de.uka.ilkd.key.core;

import java.util.EventListener;

/**
 * Event listener for interruptions. These are triggered when the user clicks on the stop button.
 */
public interface InterruptListener extends EventListener {

    void interruptionPerformed();

}
