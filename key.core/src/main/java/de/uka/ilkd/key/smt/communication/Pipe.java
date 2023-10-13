/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

/**
 * This interface describes a pipe for sending messages to or receiving them from an external SMT
 * solver process.
 *
 * @author Wolfram Pfeifer
 */
public interface Pipe {
    /**
     * Sends a message to the external process the Pipe is connected to.
     *
     * @param message the message to send
     * @throws IOException if an I/O error occurs
     */
    void sendMessage(@Nonnull String message) throws IOException;

    /**
     * Reads a message from the external process. This method blocks until there is a further
     * message or the underlying stream has been closed.
     *
     * @return the received message
     * @throws IOException if reading fails
     * @throws InterruptedException if interrupted while waiting
     */
    @Nullable
    String readMessage() throws IOException, InterruptedException;

    /**
     * Can be used to obtain the messages sent to and from the solver as well as its final result.
     *
     * @return the data sent between KeY and solver until now
     */
    @Nonnull
    SolverCommunication getSolverCommunication();

    /**
     * Forcibly closes the Pipe by destroying the process. Calling this method should be avoided if
     * possible, since the Pipe may lose messages otherwise. Most likely it is better to make the
     * process terminate normally (by sending "(exit)" to the SMT solver) and wait for the pipe to
     * automatically close.
     */
    void close();

    /**
     * Sends end-of-file to the underlying SMT solver. Note, this closes the stream.
     */
    void sendEOF();
}
