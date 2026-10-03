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
 * <li>{@link NeedsInput} - the agent asked a question ({@code ask_user}) and waits for the user
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

    /** The agent asked a question; resume with {@code AgentLoop.answerQuestion(String)}. */
    record NeedsInput(Question question) implements AgentResult {
    }

    /** A tool call awaits user approval; resume with {@code AgentLoop.decideApproval(...)}. */
    record NeedsApproval(ToolCallInfo toolCall) implements AgentResult {
    }

    /** The turn failed; {@code error} may be user-presentable via its message. */
    record Failed(Throwable error) implements AgentResult {
    }

    /** One executed tool call, rendered to the user when tool activity is shown. */
    record ToolActivity(String name, String arguments, String result) {
    }

    /** A question to be shown to the user, with optional predefined answer options. */
    record Question(
            @com.google.gson.annotations.SerializedName("question") String text,
            List<String> options) {
    }

    /** A pending tool call that awaits an approval decision. */
    record ToolCallInfo(String id, String name, String arguments) {
    }
}
