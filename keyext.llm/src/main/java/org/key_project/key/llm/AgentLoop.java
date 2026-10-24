/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CancellationException;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.key.llm.AgentResult.Question;
import org.key_project.key.llm.AgentResult.ToolActivity;
import org.key_project.key.llm.AgentResult.ToolCallInfo;
import org.key_project.key.llm.LlmContext.LlmMessage;
import org.key_project.key.llm.mcp.KeYAgentTools;

import com.google.gson.GsonBuilder;
import org.jspecify.annotations.Nullable;

/**
 * The KeY-Agent driver: runs one conversation turn as a bounded tool-calling loop and pauses for
 * user interaction (questions, tool approvals and user-initiated backgrounding of running calls).
 * <p>
 * Life cycle:
 * <ol>
 * <li>{@link #begin begin(...)} runs until a final answer ({@link AgentResult.Done}), a question
 * ({@link AgentResult.NeedsInput}), an approval request ({@link AgentResult.NeedsApproval}), a
 * background pause ({@link AgentResult.PausedForBackground}) or an error
 * ({@link AgentResult.Failed}) occurs.</li>
 * <li>On a question, the UI shows it and calls {@link #answerQuestion(String)}.</li>
 * <li>On an approval request, the UI asks the user and calls
 * {@link #decideApproval(boolean, boolean)}.</li>
 * <li>On a background pause, the running tool call continues on the {@link ToolDispatcher} pool;
 * its output is enqueued into the session's {@link TurnQueue} and this loop is resumed with
 * {@link #submitBackgroundOutput(String, String)}.</li>
 * </ol>
 * <p>
 * Every tool call is submitted to the {@link ToolDispatcher} and awaited on this loop's thread, so
 * the loop can honor {@link #cancel() cancellation} and {@link #requestBackground() backgrounding}
 * while the call runs. The messages of one round are staged (see {@code staged}) and committed to
 * the session's context only when the round resolves (a backgrounded round must not leave dangling
 * {@code tool_calls} in the context while other turns are built from it).
 *
 * @author Alexander Weigl
 */
public class AgentLoop {
    private final LlmSession session;
    private final ChatCompletionsClient completions;

    private final List<Map<String, Object>> thread = new ArrayList<>();
    /** The messages of the current round, committed to the context when the round resolves. */
    private final List<LlmMessage> staged = new ArrayList<>();
    private final List<ToolActivity> activities = new ArrayList<>();
    private AgentRequest request;
    private int rounds = 0;
    private boolean cancelled = false;
    private volatile boolean backgroundRequested = false;
    private @Nullable Pending pending;

    private interface Pending {
    }

    private record PendingApproval(String toolCallId, String name, String arguments)
            implements Pending {
    }

    private record PendingQuestion(String toolCallId, Question question) implements Pending {
    }

    private record PendingBackground(String jobId, String toolCallId, String name, String arguments)
            implements Pending {
    }

    /** The outcome of awaiting a dispatched tool call on this loop's thread. */
    private sealed interface AwaitResult permits AwaitDone, AwaitBackgrounded, AwaitCancelled {
    }

    /** The tool finished; {@code content} is the tool-result text (or an error message). */
    private record AwaitDone(String content) implements AwaitResult {
    }

    /** The user moved the call into the background (the {@link BackgroundJob} carries it). */
    private record AwaitBackgrounded(String jobId) implements AwaitResult {
    }

    /** The turn was cancelled while the call was running (the call itself keeps running). */
    private record AwaitCancelled() implements AwaitResult {
    }

    public AgentLoop(LlmSession session, ChatCompletionsClient completions) {
        this.session = session;
        this.completions = completions;
    }

    /**
     * Starts a new turn with the given raw user input. Resolves {@code $}, {@code @} and
     * {@code /} markup, assembles the request and runs the loop.
     */
    public AgentResult begin(String rawUserText, @Nullable Proof proof, @Nullable Node node,
            @Nullable Skill skill) {
        var resolver = new PromptResolver.Context() {
            @Override
            public @Nullable Proof proof() {
                return proof;
            }

            @Override
            public @Nullable Node node() {
                return node;
            }
        };
        var resolved = PromptResolver.resolve(rawUserText, session, resolver);

        // /skill: directive of this message wins; otherwise the session's active skill applies
        Skill effective =
            resolved.skillName() != null ? SkillLibrary.INSTANCE.get(resolved.skillName())
                    : skill;
        request = ExtendedPrompt.build(session, proof, node, resolved.text(), effective);
        thread.clear();
        thread.addAll(request.messages());
        staged.clear();
        activities.clear();
        rounds = 0;
        cancelled = false;
        backgroundRequested = false;
        pending = null;
        return loop();
    }

    /** Continues the turn after the user answered a question. */
    public AgentResult answerQuestion(String answer) {
        if (!(pending instanceof PendingQuestion q)) {
            return new AgentResult.Failed(new IllegalStateException("no pending question"));
        }
        pending = null;
        addToolResult(q.toolCallId(), "Answer: " + answer, false);
        return loop();
    }

    /**
     * Continues the turn after an approval decision.
     *
     * @param allow whether the tool may run
     * @param always remember the decision without further prompts for this tool
     */
    public AgentResult decideApproval(boolean allow, boolean always) {
        if (!(pending instanceof PendingApproval p)) {
            return new AgentResult.Failed(new IllegalStateException("no pending approval"));
        }
        pending = null;
        if (!allow) {
            addToolResult(p.toolCallId(),
                "[Tool call denied by the user: " + p.name() + "]", false);
            return loop();
        }
        if (always) {
            session.getMcpClient().allowWithoutApproval(p.name());
        }
        // the approved tool runs like any other: dispatched, so it can be backgrounded too
        var observer = session.getTurnObserver();
        if (observer != null) {
            observer.toolStarted(new ToolCallInfo(p.toolCallId(), p.name(), p.arguments()));
        }
        var future = session.getToolDispatcher().submit(session, p.name(), p.arguments());
        var outcome = await(future, p.toolCallId(), p.name(), p.arguments());
        if (observer != null) {
            observer.toolFinished(p.toolCallId(), outcome instanceof AwaitDone done
                    ? done.content()
                    : "[moved to background]");
        }
        return switch (outcome) {
            case AwaitDone d -> {
                addToolResult(p.toolCallId(), d.content(), true);
                yield loop();
            }
            case AwaitBackgrounded bg -> new AgentResult.PausedForBackground(bg.jobId(),
                p.name(), p.arguments());
            case AwaitCancelled ignored -> done("(Turn cancelled by the user.)");
        };
    }

    /**
     * Resumes this (parked) turn after a background tool call finished: validates that the job
     * belongs to this loop's pending background state, appends the tool result, commits the round
     * and continues the loop.
     */
    public AgentResult submitBackgroundOutput(String jobId, String content) {
        if (!(pending instanceof PendingBackground pb) || !pb.jobId().equals(jobId)) {
            return new AgentResult.Failed(
                new IllegalStateException("no pending background job " + jobId));
        }
        if (cancelled) {
            // the turn was stopped while the job was running; discard the round (it is staged
            // and therefore not part of the context)
            pending = null;
            return done("(Turn cancelled by the user.)");
        }
        pending = null;
        var msg = LlmMessage.tool(pb.toolCallId(), content);
        thread.add(msg.toOpenAiMap());
        staged.add(msg);
        activities.add(new ToolActivity(pb.name(), pb.arguments(), content));
        commitRound();
        return loop();
    }

    /**
     * Requests that the currently running (foreground) tool call be moved into the background.
     * Takes effect on this loop's next await poll. The call keeps running on the dispatcher pool;
     * the loop parks with {@link AgentResult.PausedForBackground} and is resumed when the job's
     * output arrives.
     */
    public void requestBackground() {
        backgroundRequested = true;
    }

    /** Requests cancellation; takes effect after the current await poll or HTTP call returns. */
    public void cancel() {
        cancelled = true;
    }

    public boolean isCancelled() {
        return cancelled;
    }

    public boolean hasPendingQuestion() {
        return pending instanceof PendingQuestion;
    }

    public boolean hasPendingApproval() {
        return pending instanceof PendingApproval;
    }

    /** Whether a tool-calling round is in progress (used to enable/disable the stop button). */
    public boolean isRunning() {
        return !cancelled && pending == null;
    }

    // --------------------------------------------------------------------- core loop

    private AgentResult loop() {
        int maxRounds = Math.max(1, request.maxToolRounds());
        while (true) {
            if (cancelled || Thread.currentThread().isInterrupted()) {
                return done("(Turn cancelled by the user.)");
            }
            if (rounds >= maxRounds) {
                return done("(Stopped: the maximum number of tool rounds (" + maxRounds
                    + ") was reached without a final answer.)");
            }

            final Map<String, Object> response;
            try {
                response = completions.complete(session, new AgentRequest(request.model(),
                    List.copyOf(thread), request.tools(), request.temperature(),
                    request.maxOutputTokens(), request.maxToolRounds()));
            } catch (Exception e) {
                return new AgentResult.Failed(e);
            }

            final Map<?, ?> message;
            try {
                message = extractMessage(response);
            } catch (Exception e) {
                return new AgentResult.Failed(e);
            }

            var toolCalls = asList(message.get("tool_calls"));
            String content = message.get("content") == null ? ""
                    : String.valueOf(message.get("content"));

            if (toolCalls == null || toolCalls.isEmpty()) {
                var answer = new LlmMessage("assistant", content);
                session.getContext().addMessage(answer);
                return new AgentResult.Done(content, List.copyOf(activities));
            }

            rounds++;
            var assistantMsg = LlmMessage.assistant(content, casts(toolCalls));
            thread.add(assistantMsg.toOpenAiMap());
            staged.add(assistantMsg);

            var interrupted = processBatch(casts(toolCalls));
            if (interrupted != null) {
                return interrupted; // NEEDS_INPUT, NEEDS_APPROVAL, PAUSED_FOR_BACKGROUND or
                                    // cancelled
            }
            // the round resolved: commit its messages to the context
            commitRound();
        }
    }

    /**
     * Executes a batch of tool calls (sequentially). Returns a non-null result when the turn must
     * pause for the user or stop; {@code null} when the turn can continue with the collected tool
     * results.
     */
    private @Nullable AgentResult processBatch(List<Map<String, Object>> toolCalls) {
        backgroundRequested = false;
        for (var toolCall : toolCalls) {
            var interrupted = processCall(toolCall);
            if (interrupted != null) {
                return interrupted;
            }
        }
        return null;
    }

    private @Nullable AgentResult processCall(Map<String, Object> toolCall) {
        var id = String.valueOf(toolCall.get("id"));
        Object func = toolCall.get("function");
        var function = func instanceof Map<?, ?> f ? f : Map.of();
        var name = String.valueOf(function.get("name"));
        var arguments = function.get("arguments") == null ? "{}"
                : String.valueOf(function.get("arguments"));

        if (KeYAgentTools.TOOL_ASK_USER.equals(name)) {
            if (!LlmSettings.INSTANCE.getAllowAgentQuestions()) {
                stagedTool(id, "[Asking the user is disabled in the settings]");
                return null;
            }
            // mid-batch pause: the messages up to here are part of the context (pre-existing
            // behaviour); the rest of the batch is aborted
            commitRound();
            var question = parseQuestion(arguments);
            pending = new PendingQuestion(id, question);
            return new AgentResult.NeedsInput(question);
        }

        if (KeYAgentTools.TOOL_USE_SKILL.equals(name)) {
            if (!LlmSettings.INSTANCE.getAgentCanUseSkills()) {
                stagedTool(id, "[Skills are disabled in the settings]");
                return null;
            }
            var skillName = parseSkillName(arguments);
            if (skillName == null || SkillLibrary.INSTANCE.get(skillName) == null) {
                stagedTool(id,
                    "[Unknown skill: " + (skillName == null ? "(missing name)" : skillName)
                        + "]");
                return null;
            }
            session.setActiveSkill(skillName);
            stagedTool(id, "[Skill '" + skillName + "' activated for subsequent turns]");
            return null;
        }

        if (KeYAgentTools.TOOL_SPAWN_SUBAGENT.equals(name)) {
            if (!LlmSettings.INSTANCE.getSubagentsEnabled()) {
                stagedTool(id, "[Spawning sub-agents is disabled in the settings]");
                return null;
            }
            long seqBefore = session.getSubagentLog().latestSeq();
            var observer = session.getTurnObserver();
            if (observer != null) {
                observer.toolStarted(new ToolCallInfo(id, name, arguments));
            }
            // runs without the dispatch lock: the child loops serialize their own tool calls
            var future = session.getToolDispatcher().submitTask(
                () -> SubagentRunner.run(session, completions, arguments, this::isCancelled));
            var outcome = await(future, id, name, arguments);
            if (observer != null) {
                observer.toolFinished(id, outcome instanceof AwaitDone done
                        ? done.content()
                        : "[moved to background]");
            }
            return switch (outcome) {
                case AwaitDone d -> {
                    stagedTool(id, d.content());
                    activities.add(subagentActivity(name, arguments, d.content(), seqBefore));
                    yield null;
                }
                case AwaitBackgrounded bg -> new AgentResult.PausedForBackground(bg.jobId(),
                    name, arguments);
                case AwaitCancelled ignored -> done("(Turn cancelled by the user.)");
            };
        }

        if (session.getMcpClient().requiresApproval(name)) {
            commitRound();
            pending = new PendingApproval(id, name, arguments);
            return new AgentResult.NeedsApproval(new ToolCallInfo(id, name, arguments));
        }

        var observer = session.getTurnObserver();
        if (observer != null) {
            observer.toolStarted(new ToolCallInfo(id, name, arguments));
        }
        var future = session.getToolDispatcher().submit(session, name, arguments);
        var outcome = await(future, id, name, arguments);
        if (observer != null) {
            observer.toolFinished(id, outcome instanceof AwaitDone done
                    ? done.content()
                    : "[moved to background]");
        }
        return switch (outcome) {
            case AwaitDone d -> {
                stagedTool(id, d.content());
                activities.add(new ToolActivity(name, arguments, d.content()));
                yield null;
            }
            case AwaitBackgrounded bg -> new AgentResult.PausedForBackground(bg.jobId(), name,
                arguments);
            case AwaitCancelled ignored -> done("(Turn cancelled by the user.)");
        };
    }

    /**
     * Awaits the dispatched tool call on this loop's thread, polling so that cancellation and
     * user-initiated backgrounding take effect while the call runs. The call itself is never
     * cancelled (proof tools are not interruptible); a cancelled turn simply discards the staged
     * round.
     */
    private AwaitResult await(CompletableFuture<?> future, String toolCallId, String name,
            String arguments) {
        while (true) {
            if (cancelled || Thread.currentThread().isInterrupted()) {
                return new AwaitCancelled();
            }
            if (backgroundRequested && canBackground(name)) {
                backgroundRequested = false;
                String jobId = moveToBackground(future, toolCallId, name, arguments);
                return new AwaitBackgrounded(jobId);
            }
            try {
                Object value = future.get(100, TimeUnit.MILLISECONDS);
                backgroundRequested = false;
                return new AwaitDone(stringify(value));
            } catch (TimeoutException e) {
                // poll again: cancellation / background requests are checked at the loop head
            } catch (CancellationException e) {
                backgroundRequested = false;
                return new AwaitDone("(Tool call cancelled.)");
            } catch (ExecutionException e) {
                backgroundRequested = false;
                Throwable cause = e.getCause();
                String message = cause == null || cause.getMessage() == null ? "unknown error"
                        : cause.getMessage();
                return new AwaitDone("Error calling " + name + ": " + message);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return new AwaitCancelled();
            }
        }
    }

    private boolean canBackground(String name) {
        return session.isBackgroundAllowed(name)
                && session.getBackgroundJobs().canStartMore(
                    LlmSettings.INSTANCE.getMaxBackgroundJobs());
    }

    /** Registers the running call as a background job and parks this loop on it. */
    private String moveToBackground(CompletableFuture<?> future, String toolCallId, String name,
            String arguments) {
        var job = session.getBackgroundJobs().start(this, toolCallId, name, arguments, future);
        pending = new PendingBackground(job.jobId(), toolCallId, name, arguments);
        return job.jobId();
    }

    /**
     * Builds the tool activity of a {@code spawn_subagent} call with one indented child per task
     * of every run recorded since {@code seqBefore} (the runs of this call).
     */
    private ToolActivity subagentActivity(String name, String arguments, String outcome,
            long seqBefore) {
        var children = new ArrayList<ToolActivity>();
        for (var run : session.getSubagentLog().after(seqBefore)) {
            for (var task : run.tasks()) {
                children.add(new ToolActivity(run.role(), clip(task.task(), 100),
                    run.mode() + " · " + clip(task.outcome(), 400)));
            }
        }
        return new ToolActivity(name, arguments, outcome, children);
    }

    private static String clip(String s, int max) {
        if (s == null || s.length() <= max) {
            return s;
        }
        return s.substring(0, max) + "…";
    }

    private void stagedTool(String toolCallId, String content) {
        var msg = LlmMessage.tool(toolCallId, content);
        thread.add(msg.toOpenAiMap());
        staged.add(msg);
    }

    /** Appends the staged round to the session's context (called when the round resolves). */
    private void commitRound() {
        if (!staged.isEmpty()) {
            session.getContext().addMessages(staged);
            staged.clear();
        }
    }

    private AgentResult done(String content) {
        return new AgentResult.Done(content, List.copyOf(activities));
    }

    private void addToolResult(String toolCallId, String content, boolean asActivity) {
        var msg = LlmMessage.tool(toolCallId, content);
        thread.add(msg.toOpenAiMap());
        session.getContext().addMessage(msg);
    }

    private static Question parseQuestion(String arguments) {
        try {
            var parsed = new GsonBuilder().create().fromJson(arguments, Question.class);
            return parsed == null ? new Question(arguments, List.of()) : parsed;
        } catch (Exception e) {
            return new Question(arguments, List.of());
        }
    }

    private static @Nullable String parseSkillName(String arguments) {
        try {
            var parsed = new GsonBuilder().create().fromJson(arguments, Map.class);
            if (parsed != null) {
                Object name = parsed.get("name");
                return name == null ? null : String.valueOf(name);
            }
        } catch (Exception e) {
            // fall through
        }
        return null;
    }

    static Map<?, ?> extractMessage(Map<String, Object> response) throws Exception {
        var choices = asList(response.get("choices"));
        if (choices == null || choices.isEmpty()) {
            throw new RuntimeException("The API response contains no choices.");
        }
        Object first = choices.get(0);
        if (!(first instanceof Map<?, ?> choice)) {
            throw new RuntimeException("Malformed choice in API response.");
        }
        Object message = choice.get("message");
        if (!(message instanceof Map<?, ?> m)) {
            throw new RuntimeException("Malformed message in API response.");
        }
        return m;
    }

    static String stringify(Object result) {
        if (result == null) {
            return "(no result)";
        }
        if (result instanceof String s) {
            return s;
        }
        try {
            return new GsonBuilder().create().toJson(result);
        } catch (Exception e) {
            return result.toString();
        }
    }

    @SuppressWarnings("unchecked")
    static List<Map<String, Object>> casts(List<?> toolCalls) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Object o : toolCalls) {
            if (o instanceof Map<?, ?> m) {
                result.add((Map<String, Object>) m);
            }
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    static List<?> asList(Object o) {
        return o instanceof List<?> l ? l : null;
    }
}
