// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt.communication;

import javax.annotation.Nonnull;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

/**
 * This class is responsible for starting external processes:
 * <ol>
 * <li> It creates the process (stderr is merged to stdout).</li>
 * <li> Creates the pipe that is used for communication.</li>
 * <li> Starts the process and returns. </li>
 * </ol>
 * Remark: Does not block the invoking thread.
 *
 * @author Wolfram Pfeifer (overhaul)
 */
public class ExternalProcessLauncher {
    /** the store of all messages send to and received from the external process */
    private final @Nonnull SolverCommunication session;

    /** the delimiters which separate the messages */
    private final @Nonnull  String[] messageDelimiters;

    /** the external process */
    private Process process;

    /** the pipe for sending and receiving to/from the process */
    private Pipe pipe;

    /**
     * Creates the external process launcher.
     * @param session the store for the messages send to and received from the process
     * @param messageDelimiters delimiters which separate the messages
     */
    public ExternalProcessLauncher(@Nonnull SolverCommunication session,
                                   @Nonnull String[] messageDelimiters) {
        this.session = session;
        this.messageDelimiters = messageDelimiters;
    }

    /**
     * Main procedure of the class. Starts the external process and connects the pipe to it.
     * stderr and stdout of the process are merged.
     * @param command command (program and arguments) which is used to start the external process
     * @throws IOException if an I/O error occurs
     */
    public void launch(final String [] command) throws IOException {
        try {
            ProcessBuilder builder = new ProcessBuilder(command);
            builder.redirectErrorStream(true);
            process = builder.start();
            InputStream input = process.getInputStream();
            OutputStream output = process.getOutputStream();
            pipe = new SimplePipe(input, messageDelimiters, output, session, process);
        } catch (Exception ex) {
            stop();
            throw ex;
        }
    }

    /**
     * Stops the external process: In particular the pipe is closed and the process is destroyed.
     */
    public void stop() {
        if(process != null) {
            process.destroy();
        }
        // TODO: where to close the pipe?
        //pipe.close();
    }

    public Pipe getPipe() {
        return pipe;
    }
}