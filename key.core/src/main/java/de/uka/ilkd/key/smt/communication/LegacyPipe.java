/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;


import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.smt.communication.SolverCommunication.Message;
import de.uka.ilkd.key.smt.communication.SolverCommunication.MessageType;

/**
 * On each side of the pipe there are sender and receivers: **** Receiver ====<=Output======= Sender
 * ****************** KeY* Sender ======Input=>====== Receiver *External Process* **** Receiver
 * ====<=Error======== Sender ******************
 *
 * @author Benjamin Niedermann (original)
 * @author Mattias Ulbrich (ovrhaul)
 * @author Wolfram Pfeifer (extracted interface, marked as legacy)
 */
@Deprecated
class LegacyPipe implements Pipe {
    /**
     * The workers of the pipe. One worker is responsible for sending messages, while the other two
     * workers handle messages which are received.
     */
    private Receiver stdoutReceiver;
    private Receiver stderrReceiver;

    /**
     * The delimiters of the messages, i.e. strings that indicate the end of a message. If you
     * specify several delimiters a single message is chosen as small as possible, i.e., it does not
     * contain any delimiter.
     */
    private final String[] messageDelimiters;

    private static final Message EXCEPTION_MESSAGE = new Message("Exception", MessageType.ERROR);

    private static final Message STREAM_CLOSED_MESSAGE =
        new Message("Stream closed", MessageType.ERROR);

    /**
     * User specific data.
     */
    private final SolverCommunication session;
    private OutputStreamWriter outputWriter;
    private final BlockingQueue<Message> messageQueue = new LinkedBlockingQueue<>();
    private Exception thrownException;
    private Process process;


    public LegacyPipe(SolverCommunication session, String[] messageDelimiters) {
        this.session = session;
        this.messageDelimiters = messageDelimiters;
    }

    /**
     * Waits until a message is received from the other side of the pipe. Then it forwards the
     * message to its listeners and waits again until the next message is received.
     */
    private class Receiver extends Thread {
        private final InputStream input;
        private final MessageType type;
        private boolean alive = true;

        public Receiver(InputStream input, MessageType type, String name) {
            super(name);
            this.input = input;
            this.type = type;
        }

        @Override
        public void run() {

            // do not use BufferedReader, but this wrapper in order to support different
            // message delimiters.
            BufferedMessageReader reader =
                new BufferedMessageReader(new InputStreamReader(input, StandardCharsets.UTF_8),
                    messageDelimiters);

            try {

                while (true) {
                    if (Thread.interrupted()) {
                        break;
                    }
                    // this call blocks the thread and waits until there is a message.
                    String message = reader.readMessage();
                    if (message == null) {
                        // message null indicates EOF.
                        break;
                    }
                    deliverMessage(message, type);
                }

            } catch (InterruptedIOException ex) {
                // Interruption is ok and needs not be reported
            } catch (IOException e) {
                close();
                thrownException = e;
                messageQueue.add(EXCEPTION_MESSAGE);
            } finally {
                try {
                    String buf = reader.drain();
                    if (buf != null && !buf.isEmpty()) {
                        deliverMessage(buf, type);
                    }
                    input.close();
                } catch (IOException ex) {
                    // considered harmless.
                }
                alive = false;
                messageQueue.add(STREAM_CLOSED_MESSAGE);
            }
        }
    }

    private void deliverMessage(String buf, MessageType type) {
        assert buf != null;
        Message message = new Message(buf, type);
        messageQueue.add(message);
    }

    public void start(Process process) {

        InputStream stdout = process.getInputStream();
        OutputStream stdin = process.getOutputStream();
        InputStream stderr = process.getErrorStream();

        this.process = process;
        this.outputWriter = new OutputStreamWriter(stdin, StandardCharsets.UTF_8);

        stdoutReceiver = new Receiver(stdout, MessageType.OUTPUT, "receiver for normal messages");
        stderrReceiver = new Receiver(stderr, MessageType.ERROR, "receiver for stderr messages");

        stdoutReceiver.setDaemon(true);
        stdoutReceiver.start();

        stderrReceiver.setDaemon(true);
        stderrReceiver.start();
    }

    public void close() {
        stdoutReceiver.interrupt();
        stderrReceiver.interrupt();
        process.destroy();
    }

    @Override
    public void sendEOF() {
        // not used anymore
    }

    public void join() throws InterruptedException {
        stdoutReceiver.join();
        stderrReceiver.join();
    }

    @Override
    public synchronized void sendMessage(@Nonnull String message) throws IOException {
        outputWriter.write(message + System.lineSeparator());
        outputWriter.flush();
    }


    @Override
    public @Nullable String readMessage() throws IOException, InterruptedException {
        while (isAlive()) {
            Message result = messageQueue.take();
            if (result == EXCEPTION_MESSAGE) {
                // Special indicator for a raised exception.
                if (thrownException instanceof IOException) {
                    throw (IOException) thrownException;
                } else {
                    throw new IOException(thrownException);
                }
            } else if (result == STREAM_CLOSED_MESSAGE) {
                // This is a mere indicator to run isAlive once more ...
            } else {
                // just to fix compile problems, the message type is completely thrown away here
                // (the class only exists as unused legacy code)
                return result.getContent();
            }
        }
        return null;
    }

    public boolean isAlive() {
        return stderrReceiver.alive && stdoutReceiver.alive;
    }

    public @Nonnull SolverCommunication getSolverCommunication() {
        return session;
    }
}
