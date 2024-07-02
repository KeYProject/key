package de.uka.ilkd.key.smt.communication;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.st.SolverType;

import javax.annotation.Nonnull;
import java.io.IOException;

/**
 * The socket for CVC4.
 *
 * @author Wolfram Pfeifer (overhaul)
 */
public class CVC4Socket extends AbstractSolverSocket {
    /**
     * Creates a new CVC4Socket. Should not be called directly, better use the static factory method
     * {@link AbstractSolverSocket#createSocket(SolverType, ModelExtractor)}.
     *
     * @param name  the name of the solver
     * @param query the ModelExtractor for CE generation (unused by this socket)
     */
    public CVC4Socket(String name, ModelExtractor query) {
        super(name, query);
    }

    @Override
    public void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg) throws IOException {
        SolverCommunication sc = pipe.getSolverCommunication();
        if ("".equals(msg)) {
            return;
        }

        // used only to steer the interaction with the solver and thus filtered out currently
        if (!msg.contains("success")) {
            sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
        }

        if (msg.contains("error") || msg.contains("Error")) {
            sc.addMessage(msg, SolverCommunication.MessageType.ERROR);
            throw new IOException("Error while executing CVC4: " + msg);
        }

        // Currently we rely on the solver to terminate after receiving "(exit)". If this does
        // not work in future, it may be that we have to forcibly close the pipe.
        if (sc.getState() == WAIT_FOR_RESULT) {
            if (msg.contains("\n" + "unsat")) {
                sc.setFinalResult(SMTSolverResult.createValidResult(getName()));
                sc.setState(FINISH);
                pipe.sendMessage("(exit)");
//                pipe.close();
            } else if (msg.contains("\n" + "sat")) {
                sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
                sc.setState(FINISH);
                pipe.sendMessage("(exit)");
//                pipe.close();
            } else if (msg.contains("\n" + "unknown")) {
                sc.setFinalResult(SMTSolverResult.createUnknownResult(getName()));
                sc.setState(FINISH);
                pipe.sendMessage("(exit)");
//                pipe.close();
            }
        }
    }
}
