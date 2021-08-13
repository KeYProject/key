package de.uka.ilkd.key.smt.communication;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.*;

/**
 * This class represents a simplified version of the existing pipe. It assumes that the external
 * process merges stderr and stdout (see {@link ExternalProcessLauncher}).
 *
 * @author Wolfram Pfeifer
 */
public class SimplePipe implements Pipe {
    /** The Reader that splits incoming messages at the given delimiters. */
    private final @Nonnull BufferedMessageReader reader;

    /**  */
    private final @Nonnull SolverCommunication session;

    /** The process this pipe is attached to. */
    private final @Nonnull Process process;

    /** The OutputStreamWriter connected to stdin of the external process. */
    private final @Nonnull OutputStreamWriter outputStreamWriter;

    /**
     * Creates a new SimplePipe.
     * @param input the InputStream connected to the merged stdout and stderr of the external
     *              process
     * @param messageDelimiters the delimiters which separate one message from another
     * @param output the OutputStream connected to stdin of the external process
     * @param session the message list where to log the messages to
     * @param process the external process this pipe is connected to
     */
    public SimplePipe(@Nonnull InputStream input, @Nonnull String[] messageDelimiters,
                      @Nonnull OutputStream output, @Nonnull SolverCommunication session,
                      @Nonnull Process process) {
        this.session = session;
        this.process = process;
        reader = new BufferedMessageReader(new InputStreamReader(input), messageDelimiters);
        outputStreamWriter = new OutputStreamWriter(output);
    }

    @Override
    public void sendMessage(@Nonnull String message) throws IOException {
        session.addMessage(message, SolverCommunication.MessageType.INPUT);
        outputStreamWriter.write(message + System.lineSeparator());
        outputStreamWriter.flush();
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
        process.destroy();
    }
}
