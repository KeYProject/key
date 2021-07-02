package de.uka.ilkd.key.smt;

import java.io.*;

public class SimplePipe implements Pipe {
    private final BufferedMessageReader reader;
    private final OutputStreamWriter outputStreamWriter;
    private final SolverCommunication session;
    private final Process process;

    public SimplePipe(InputStream input, String[] messageDelimiters, OutputStream output,
                      SolverCommunication session, Process process) {
        this.session = session;
        this.process = process;
        reader = new BufferedMessageReader(new InputStreamReader(input), messageDelimiters);
        outputStreamWriter = new OutputStreamWriter(output);
    }

    @Override
    public void sendMessage(String message) throws IOException {
        outputStreamWriter.write(message + System.lineSeparator());
        outputStreamWriter.flush();
    }

    @Override
    public SolverCommunication.Message readMessage() throws IOException, InterruptedException {
        String messageStr = reader.readMessage();
        if (messageStr != null) {
            SolverCommunication.Message message = new SolverCommunication.Message(messageStr,
                SolverCommunication.MessageType.Output);
            return message;
        }

        return null;
    }

    @Override
    public SolverCommunication getSession() {
        return session;
    }

    @Override
    public void close() {
        process.destroy();
    }
}
