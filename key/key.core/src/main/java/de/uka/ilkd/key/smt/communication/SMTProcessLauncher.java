package de.uka.ilkd.key.smt.communication;

import java.io.IOException;

/**
 * Launches an SMT solver process in some way.
 * The mostly used implementation of this is {@link ExternalProcessLauncher}, but there may be solvers that need
 * different approaches as the standard input/output communication doesn't work.
 */
public interface SMTProcessLauncher {


    /**
     * Every SMT process launcher initializes a pipe that can send and receive messages from
     * @return the {@link Pipe} used to send and receive messages from the process started by this launcher
     */
    Pipe getPipe();

    void launch(String[] commands) throws IOException;

    void stop();
}
