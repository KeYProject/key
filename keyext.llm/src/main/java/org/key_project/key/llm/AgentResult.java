/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;

/**
 * The outcome of one step (or the whole turn) of the KeY-Agent loop.
 * <p>
 * A turn ends in one of four ways:
 * <ul>
 * <li>{@link Done} - a final (non tool-calling) answer was produced.</li>
 * <li>{@link NeedsInput} - the agent asked a question ({@code question}) and waits for the user
 * to answer before continuing.</li>
 * <li>{@link NeedsApproval} - the agent wants to call a tool that requires user approval and
 * waits for a decision.</li>
 * <li>{@link Failed} - an error occurred (transport, API error, tool limit).</li>
 * </ul>
 */
public sealed interface AgentResult {

    /** The agent produced a final answer. */
    record Done(String content, List<ToolActivity> activities) implements AgentResult {
    }

    /**
     * The agent asked one or more questions; resume with {@code AgentLoop.answerQuestion(String)}.
     */
    record NeedsInput(List<Question> questions) implements AgentResult {
    }

    /** A tool call awaits user approval; resume with {@code AgentLoop.decideApproval(...)}. */
    record NeedsApproval(ToolCallInfo toolCall) implements AgentResult {
    }

    /**
     * A running tool call was moved into the background by the user. The turn of this loop is
     * parked in the session; when the background job finishes, its output is enqueued into the
     * session's {@link TurnQueue} and the turn is resumed with
     * {@code AgentLoop.submitBackgroundOutput(jobId, content)}.
     */
    record PausedForBackground(String jobId, String toolName, String arguments)
            implements AgentResult {
    }

    /** The turn failed; {@code error} may be user-presentable via its message. */
    record Failed(Throwable error) implements AgentResult {
    }

    /**
     * One executed tool call, rendered to the user when tool activity is shown. {@code children}
     * holds the indented sub-activity of a {@code subagent} call (one entry per delegated
     * task).
     */
    record ToolActivity(String name, String arguments, String result,
            List<ToolActivity> children) {

        ToolActivity(String name, String arguments, String result) {
            this(name, arguments, result, List.of());
        }
    }

    /**
     * One question shown to the user (the {@code question} tool, following OpenCode's schema):
     * an optional short header (at most 30 characters, used as the dialog title), the question
     * text, predefined answer options with an optional explanation each, and whether several
     * options may be selected. The user can always answer with free text instead.
     */
    record Question(String header, String text, List<Option> options, boolean multiple) {

        /** A predefined answer option: a short label plus an optional explanation. */
        record Option(String label, String description) {
        }

        /** A plain question without header, options or multiple choice. */
        public Question(String text) {
            this(null, text, List.of(), false);
        }
    }

    /** A pending tool call that awaits an approval decision. */
    record ToolCallInfo(String id, String name, String arguments) {
    }
}
