package de.uka.ilkd.key.smt.communication;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.st.SolverType;

import javax.annotation.Nonnull;
import java.io.IOException;

/**
 * The SolverSocket class describes the communication between the KeY and the SMT solver process.
 * This description is no longer part of the SolverType because in the case when we search for
 * counterexamples and one is found, the model has to be queried. This query depends on the SMT
 * problem and is not the same for all solvers of a given type.
 *
 * @author mihai
 * @author Wolfram Pfeifer (overhaul, removed legacy solvers)
 */
public class SolverSocket {
    /** Indicates that the solver has not yet sent a sat/unsat/unknown result. */
    protected static final int WAIT_FOR_RESULT = 0;

    /** Indicates that the socket waits for more details (a model or a proof). */
    protected static final int WAIT_FOR_DETAILS = 1;

    /** Indicates that the socket waits for the result to a query (used by CE generator). */
    protected static final int WAIT_FOR_QUERY = 2;

    /** Indicates that the socket waits for a model to be produced by the solver. This is a special
     * version of WAIT_FOR_DETAILS only used by the CE generator. */
    protected static final int WAIT_FOR_MODEL = 3;

    /** Indicates that the solver already sent a sat/unsat/unknown result. */
    protected static final int FINISH = 4;

    /** The name of the solver related to the socket. */
    private final String name;

    /** The ModelExtractor that is to be used for CE generation (only used for CE socket). */
    private ModelExtractor query;

    /** The {@link MessageHandler} message handler of this socket */
    private MessageHandler handler;

    /**
     * Creates a new solver socket with given solver name and ModelExtractor.
     * @param name the name of the solver in use
     * @param query the ModelExtractor used to extract a counterexample
     */
    public SolverSocket(@Nonnull String name, ModelExtractor query, MessageHandler handler) {
        this.name = name;
        this.query = query;
        this.handler = handler;
    }

    public ModelExtractor getQuery() {
        return query;
    }

    public void setQuery(ModelExtractor query) {
        this.query = query;
    }

    protected String getName() {
        return name;
    }

    /**
     * Invoked when the solver has sent a new message to its stdout or stderr.
     * @param pipe the Pipe that received the message
     * @param msg the message as String
     * @throws IOException if an I/O error occurs
     */
    public void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg) throws IOException {
        handler.messageIncoming(pipe, msg, this);
    }

    /**
     * Creates a new solver socket that can handle the communication for the given solver type.
     * @param type the SolverType to create the socket for
     * @param query the ModelExtractor that can be used to extract a counterexample (for non-CE
     *              solvers this can be null)
     * @return the newly created socket
     */
    public static @Nonnull
    SolverSocket createSocket(@Nonnull SolverType type, ModelExtractor query) {
        return type.getSocket(query);
    }

    public enum MessageHandler {

        DEFAULT {
            @Override
            public void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg, @Nonnull SolverSocket socket) throws IOException {
                SolverCommunication sc = pipe.getSolverCommunication();
                if (msg.startsWith("(error")) {
                    sc.addMessage(msg, SolverCommunication.MessageType.ERROR);
                    if (msg.contains("WARNING:")) {
                        return;
                    }
                    throw new IOException("Error while executing " + socket.getName() + ": " + msg);
                }

                // used only to steer the interaction with the solver and thus filtered out currently
                if (!msg.equals("success")) {
                    sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
                }

                switch (sc.getState()) {
                    case WAIT_FOR_RESULT:
                        if (msg.equals("unsat")) {
                            sc.setFinalResult(SMTSolverResult.createValidResult(socket.getName()));
                            // TODO: proof production is currently completely disabled, since it does not work
                            //  with the legacy Z3 translation (proof-production not enabled) and also not
                            //  really needed
                            // pipe.sendMessage("(get-proof)");

                            pipe.sendMessage("(exit)");
                            sc.setState(WAIT_FOR_DETAILS);
                        }
                        if (msg.equals("sat")) {
                            sc.setFinalResult(SMTSolverResult.createInvalidResult(socket.getName()));
                            pipe.sendMessage("(get-model)");
                            pipe.sendMessage("(exit)");
                            sc.setState(WAIT_FOR_DETAILS);

                        }
                        if (msg.equals("unknown")) {
                            sc.setFinalResult(SMTSolverResult.createUnknownResult(socket.getName()));
                            pipe.sendMessage("(exit)\n");
                            sc.setState(WAIT_FOR_DETAILS);
                        }
                        break;

                    case WAIT_FOR_DETAILS:
                        // Currently we rely on the solver to terminate after receiving "(exit)". If this does
                        // not work in future, it may be that we have to forcibly close the pipe.
//            if (msg.equals("success")) {
//                pipe.sendMessage("(exit)");
//                pipe.close();
//            }
                        break;
                }
            }
        },

        CVC4 {
            @Override
            public void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg, @Nonnull SolverSocket socket) throws IOException {
                SolverCommunication sc = pipe.getSolverCommunication();
                if ("".equals(msg.trim())) {
                    return;
                }

                // used only to steer the interaction with the solver and thus filtered out currently
                if (!msg.contains("success")) {
                    sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
                }

                if (msg.contains("error") || msg.contains("Error")) {
                    sc.addMessage(msg, SolverCommunication.MessageType.ERROR);
                    throw new IOException("Error while executing " + socket.getName() + ": " + msg);
                }

                // Currently we rely on the solver to terminate after receiving "(exit)". If this does
                // not work in future, it may be that we have to forcibly close the pipe.
                if (sc.getState() == WAIT_FOR_RESULT) {
                    if (msg.contains("\n" + "unsat")) {
                        sc.setFinalResult(SMTSolverResult.createValidResult(socket.getName()));
                        sc.setState(FINISH);
                        pipe.sendMessage("(exit)");
//                pipe.close();
                    } else if (msg.contains("\n" + "sat")) {
                        sc.setFinalResult(SMTSolverResult.createInvalidResult(socket.getName()));
                        sc.setState(FINISH);
                        pipe.sendMessage("(exit)");
//                pipe.close();
                    } else if (msg.contains("\n" + "unknown")) {
                        sc.setFinalResult(SMTSolverResult.createUnknownResult(socket.getName()));
                        sc.setState(FINISH);
                        pipe.sendMessage("(exit)");
//                pipe.close();
                    }
                }
            }
        },

        CVC5 {
            @Override
            public void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg, @Nonnull SolverSocket socket) throws IOException {
                SolverCommunication sc = pipe.getSolverCommunication();
                if ("".equals(msg.trim())) {
                    return;
                }

                // used only to steer the interaction with the solver and thus filtered out currently
                if (!msg.contains("success")) {
                    sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
                }

                if (msg.contains("error") || msg.contains("Error")) {
                    sc.addMessage(msg, SolverCommunication.MessageType.ERROR);
                    throw new IOException("Error while executing " + socket.getName() + ": " + msg);
                }

                // Currently we rely on the solver to terminate after receiving "(exit)". If this does
                // not work in future, it may be that we have to forcibly close the pipe.
                if (sc.getState() == WAIT_FOR_RESULT) {
                    if (msg.contains("unsat")) {
                        sc.setFinalResult(SMTSolverResult.createValidResult(socket.getName()));
                        sc.setState(FINISH);
                        pipe.sendMessage("(exit)");
                        //pipe.close();
                    } else if (msg.contains("sat")) {
                        sc.setFinalResult(SMTSolverResult.createInvalidResult(socket.getName()));
                        sc.setState(FINISH);
                        pipe.sendMessage("(exit)");
                        //pipe.close();
                    } else if (msg.contains("unknown")) {
                        sc.setFinalResult(SMTSolverResult.createUnknownResult(socket.getName()));
                        sc.setState(FINISH);
                        pipe.sendMessage("(exit)");
                        //pipe.close();
                    }
                }
            }
        },

        Z3CE {
            @Override
            public void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg, @Nonnull SolverSocket socket) throws IOException {
                SolverCommunication sc = pipe.getSolverCommunication();

                if (msg.startsWith("(error")) {
                    sc.addMessage(msg, SolverCommunication.MessageType.ERROR);
                    if (msg.contains("WARNING:")) {
                        return;
                    }
                    throw new IOException("Error while executing " + socket.getName() + ": " + msg);
                }
                // These two messages are only used to steer the interaction with the solver and are thus
                // currently filtered out to avoid cluttering up the output.
                if (!msg.equals("success") && !msg.equals("endmodel")) {
                    sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
                }

                switch (sc.getState()) {
                    case WAIT_FOR_RESULT:
                        if (msg.equals("unsat")) {
                            sc.setFinalResult(SMTSolverResult.createValidResult(socket.getName()));
                            pipe.sendMessage("(exit)");
                            sc.setState(WAIT_FOR_DETAILS);
                        }
                        if (msg.equals("sat")) {
                            sc.setFinalResult(SMTSolverResult.createInvalidResult(socket.getName()));
                            pipe.sendMessage("(get-model)");
                            pipe.sendMessage("(echo \"endmodel\")");
                            sc.setState(WAIT_FOR_MODEL);
                        }
                        if (msg.equals("unknown")) {
                            sc.setFinalResult(SMTSolverResult.createUnknownResult(socket.getName()));
                            sc.setState(WAIT_FOR_DETAILS);
                            pipe.sendMessage("(exit)");
                        }

                        break;

                    case WAIT_FOR_DETAILS:
                        // Currently we rely on the solver to terminate after receiving "(exit)". If this does
                        // not work in future, it may be that we have to forcibly close the pipe.
                        break;

                    case WAIT_FOR_QUERY:
                        if (!msg.equals("success")) {
                            socket.getQuery().messageIncoming(pipe, msg);
                        }
                        break;

                    case WAIT_FOR_MODEL:
                        if (msg.equals("endmodel")) {
                            if (socket.getQuery() != null && socket.getQuery().getState() == ModelExtractor.DEFAULT) {
                                socket.getQuery().getModel().setEmpty(false);
                                socket.getQuery().start(pipe);
                                sc.setState(WAIT_FOR_QUERY);
                            } else {
                                pipe.sendMessage("(exit)\n");
                                sc.setState(WAIT_FOR_DETAILS);
                            }
                        }
                        break;
                    default:
                        throw new IllegalStateException("Unexpected value: " + sc.getState());
                }
            }
        };

        MessageHandler() {}

        public abstract void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg, @Nonnull SolverSocket socket) throws IOException;

    }
}

