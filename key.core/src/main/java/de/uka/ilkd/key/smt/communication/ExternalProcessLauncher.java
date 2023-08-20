/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.*;
import javax.annotation.Nonnull;

/**
 * This class is responsible for starting external processes:
 * <ol>
 * <li>It creates the process (stderr is merged to stdout).</li>
 * <li>Creates the pipe that is used for communication.</li>
 * <li>Starts the process and returns.</li>
 * </ol>
 * Remark: Does not block the invoking thread.
 *
 * @author Wolfram Pfeifer (overhaul)
 */
public class ExternalProcessLauncher {
    /**
     * the store of all messages send to and received from the external process
     */
    private final @Nonnull SolverCommunication session;

    /**
     * the delimiters which separate the messages
     */
    private final @Nonnull String[] messageDelimiters;

    /**
     * the external process
     */
    private Process process;

    /**
     * the pipe for sending and receiving to/from the process
     */
    private SimplePipe pipe;

    /**
     * Creates the external process launcher.
     *
     * @param session the store for the messages send to and received from the process
     * @param messageDelimiters delimiters which separate the messages
     */
    public ExternalProcessLauncher(@Nonnull SolverCommunication session,
            @Nonnull String[] messageDelimiters) {
        this.session = session;
        this.messageDelimiters = messageDelimiters;
    }

    /**
     * Main procedure of the class. Starts the external process and connects the pipe to it. stderr
     * and stdout of the process are merged.
     *
     * @param command command (program and arguments) which is used to start the external process
     * @throws IOException if an I/O error occurs
     */
    public void launch(final String[] command) throws IOException {
        try {
            ProcessBuilder builder = new ProcessBuilder(command);
            builder.redirectErrorStream(true);
            process = builder.start();
            InputStream input = process.getInputStream();
            OutputStream output = process.getOutputStream();
            pipe = new SimplePipe(input, messageDelimiters, output, session, process);
        } catch (IOException ex) {
            stop();
            throw ex;
        }
    }

    /**
     * Stops the external process: In particular the pipe is closed and the process is destroyed.
     */
    public void stop() {
        if (process != null) {
            process.destroy();
        }
        // TODO: where to close the pipe?
        // pipe.close();
    }

    public Pipe getPipe() {
        return pipe;
    }
}
