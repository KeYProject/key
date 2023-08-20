/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.*;
import java.nio.charset.StandardCharsets;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class represents a simplified version of the existing pipe. It assumes that the external
 * process merges stderr and stdout (see {@link ExternalProcessLauncher}).
 *
 * @author Wolfram Pfeifer
 */
public class SimplePipe implements Pipe {
    private static final Logger LOGGER = LoggerFactory.getLogger(SimplePipe.class);

    /**
     * The Reader that splits incoming messages at the given delimiters.
     */
    private final @Nonnull BufferedMessageReader reader;

    /**
     *
     */
    private final @Nonnull SolverCommunication session;

    /**
     * The process this pipe is attached to.
     */
    private final @Nonnull Process process;

    /**
     * The Writer connected to stdin of the external process.
     */
    private final @Nonnull Writer smtIn;

    /**
     * Input of the SMT stdin
     */
    private final Writer processWriter;

    /**
     * Input of the SMT stdout. Use with care in error cases. The output stream is owned by
     * {@link BufferedMessageReader}.
     */
    private final TeeReader processReader;

    /**
     * Capture of the stdin of the SMT process
     */
    private final StringWriter stdin = new StringWriter();

    /**
     * Capture of the stdout of the SMT process
     */
    private final StringWriter stdout = new StringWriter();


    /**
     * Creates a new SimplePipe.
     *
     * @param input the InputStream connected to the merged stdout and stderr of the external
     *        process
     * @param messageDelimiters the delimiters which separate one message from another
     * @param output the OutputStream connected to stdin of the external process
     * @param session the message list where to log the messages to
     * @param process the external process this pipe is connected to
     */
    public SimplePipe(@Nonnull InputStream input, @Nonnull String[] messageDelimiters,
            @Nonnull OutputStream output, @Nonnull SolverCommunication session,
            @Nonnull Process process) {
        processWriter =
            new TeeWriter(new OutputStreamWriter(output, StandardCharsets.UTF_8), stdin);
        processReader = new TeeReader(new InputStreamReader(input, StandardCharsets.UTF_8), stdout);

        this.session = session;
        this.process = process;
        reader = new BufferedMessageReader(processReader, messageDelimiters);
        smtIn = processWriter;
    }

    public String getSentMessages() {
        return stdin.toString();
    }

    public String getReadMessages() {
        return stdout.toString();
    }

    @Override
    public void sendMessage(@Nonnull String message) throws IOException {
        try {
            session.addMessage(message, SolverCommunication.MessageType.INPUT);
            smtIn.write(message + System.lineSeparator());
            smtIn.flush();
        } catch (IOException e) {
            if (!process.isAlive()) {
                tryToReadExhaustively();
                int exit = process.exitValue();
                throw new IllegalStateException("Process terminated (exit code " + exit
                    + "). Process report:\n" + getReadMessages());
            } else {
                throw e;
            }
        }
    }

    public void tryToReadExhaustively() {
        try {
            while (-1 != processReader.read()) {
                /* empty */
            }
        } catch (IOException ignore) {
        }
    }

    @Override
    public @Nullable String readMessage() throws IOException, InterruptedException {
        // blocks if there is currently no message
        return reader.readMessage();
    }

    @Override
    public @Nonnull SolverCommunication getSolverCommunication() {
        return session;
    }

    @Override
    public void close() {
        try {
            processReader.close();
        } catch (IOException e) {
            LOGGER.warn("Failed to close process reader", e);
        }

        try {
            processWriter.close();
        } catch (IOException e) {
            LOGGER.warn("Failed to close process writer", e);
        }

        process.destroy();
    }

    @Override
    public void sendEOF() {
        try {
            processWriter.close();
        } catch (IOException e) {
            LOGGER.warn("Failed to close process writer", e);
        }
    }
}
