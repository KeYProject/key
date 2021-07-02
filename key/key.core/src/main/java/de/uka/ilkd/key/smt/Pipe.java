package de.uka.ilkd.key.smt;

import java.io.IOException;

public interface Pipe {
    void sendMessage(String message) throws IOException;

    SolverCommunication.Message readMessage() throws IOException, InterruptedException;

    SolverCommunication getSession();

    void close();
}
