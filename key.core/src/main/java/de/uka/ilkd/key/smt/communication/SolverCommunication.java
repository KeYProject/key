/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.smt.SMTSolverResult;

/**
 * Stores the communication between KeY and an external solver: Contains a list that stores the
 * messages that have been sent from the solver to KeY and vice versa. Further, it also contains the
 * final result of the solver. <br>
 * <br>
 * <b>Note:</b> The solver outputs "endmodel" and "success" are currently not stored, since they are
 * used solely to steer the interaction between solver and KeY.
 *
 * @author Benjamin Niedermann
 * @author Wolfram Pfeifer (overhaul)
 */
public class SolverCommunication {
    /** All messages (input/output/error) sent between KeY and SMT solver. */
    private final List<Message> messages = Collections.synchronizedList(new LinkedList<>());

    /** The final result of the associated solver (unknown if not yet set). */
    private SMTSolverResult finalResult = SMTSolverResult.NO_IDEA;

    /** The current state of the communication. The states are defined by the solver sockets. */
    private int state = 0;

    /**
     * The message type depends on the channel which was used for sending the message.
     */
    public enum MessageType {
        /** a message that has been sent from KeY to the solver */
        INPUT,
        /** a non-error message that has been sent from the solver to KeY */
        OUTPUT,
        /** an error message that has been sent from the solver to KeY */
        ERROR
    }

    /**
     * Represents a single message sent from or to the solver.
     */
    public static final class Message {
        /** the text of the message */
        private final String content;

        /** the type of the message (INPUT/OUTPUT/ERROR) */
        private final MessageType type;

        /**
         * Creates a new message.
         *
         * @param content the text of the new message
         * @param type the type of the new message
         */
        public Message(String content, MessageType type) {
            this.content = content;
            this.type = type;
        }

        public String getContent() {
            return content;
        }

        public MessageType getType() {
            return type;
        }
    }

    /**
     * Returns all messages that were sent between KeY and the solver. Note that, input and output
     * messages are interwoven but in order.
     *
     * @return all messages sent in both directions
     */
    public Iterable<Message> getMessages() {
        // wrap into an unmodifiable list to prohibit changes to the messages list
        return Collections.unmodifiableList(messages);
    }

    /**
     * Returns a new Iterable (can not be used to change the message list of SolverCommunication)
     * containing all the sent messages of the given type.
     *
     * @param type the type to filter the messages for
     * @return a new Iterable containing all messages of the given type
     */
    public Iterable<Message> getMessages(MessageType type) {
        // since we stream from a list, the original order is maintained
        return messages.stream().sequential().filter(m -> m.getType() == type)
                // ACTIVATE WHEN Java 11: // .collect(Collectors.toUnmodifiableList());
                .collect(Collectors.toList());
    }

    /**
     * Returns a new Iterable (can not be used to change the message list of SolverCommunication)
     * containing all the output messages sent by the solver (including error messages!).
     *
     * @return a new Iterable containing all output messages of the solver
     */
    public Iterable<Message> getOutMessages() {
        // since we stream from a list, the original order is maintained
        return messages.stream().sequential()
                .filter(m -> m.getType() == MessageType.OUTPUT || m.getType() == MessageType.ERROR)
                // ACTIVATE WHEN Java 11: // .collect(Collectors.toUnmodifiableList());
                .collect(Collectors.toList());
    }

    /**
     * Adds a message to the communication log.
     *
     * @param message the text of the message to add
     * @param type the type of the message to add
     */
    void addMessage(String message, MessageType type) {
        messages.add(new Message(message, type));
    }

    public SMTSolverResult getFinalResult() {
        return finalResult;
    }

    void setFinalResult(SMTSolverResult finalResult) {
        this.finalResult = finalResult;
    }

    public int getState() {
        return state;
    }

    void setState(int state) {
        this.state = state;
    }
}
