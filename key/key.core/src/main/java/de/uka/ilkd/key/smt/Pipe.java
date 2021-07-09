package de.uka.ilkd.key.smt;

import javax.annotation.Nonnull;
import java.io.IOException;

/**
 * This interface describes a pipe for sending messages to or receiving them from an external
 * process.
 *
 * @author Wolfram Pfeifer
 */
public interface Pipe {
    /**
     * Sends a message to the external process the Pipe is connected to.
     * @param message the message to send
     * @throws IOException if an I/O error occurs
     */
    void sendMessage(@Nonnull String message) throws IOException;

    /**
     * Reads a message from the external process. This method blocks until there is a further
     * message or the underlying stream has been closed.
     * @return the received message
     * @throws IOException if reading fails
     * @throws InterruptedException if interrupted while waiting
     */
    @Nonnull String readMessage() throws IOException, InterruptedException;

    /**
     *
     * @return
     */
    @Nonnull SolverCommunication getSession();

    /**
     * Forcibly closes the Pipe by destroying the process. Calling this method should be avoided if
     * possible, since then the Pipe may lose messages or even. Most likely it is
     * better to make the process terminate normally (e.g. by sending "(exit)" in case of SMT
     * solvers) and wait for the pipe to automatically close.
     */
    void close();
}
