/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import org.key_project.key.llm.LlmSession;
import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.ToolFacade;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless tests of the {@code execute} tool: the safety gate, the JShell evaluation with the
 * bound {@code tools} facade (dispatching real tool calls through the session's MCP client),
 * timeouts, output bounds and the tool metadata.
 *
 * @author Alexander Weigl
 */
class ScriptingToolsTest {

    private LlmSession session;
    private ToolFacade facade;
    private boolean unrestricted;

    @BeforeEach
    void setUp() {
        session = new LlmSession("https://example.invalid", "token", "model");
        facade = new ToolFacade(session);
        var settings = LlmSettings.INSTANCE;
        unrestricted = settings.getUnrestrictedExecute();
        settings.setUnrestrictedExecute(false);
        settings.setExecuteTimeoutSeconds(20);
        settings.setExecuteMaxOutputChars(65536);
    }

    @AfterEach
    void tearDown() {
        LlmSettings.INSTANCE.setUnrestrictedExecute(unrestricted);
    }

    // ------------------------------------------------------------------ safety gate

    @Test
    void restrictedModeRejectsRawJvmAccess() {
        assertNull(ScriptingTools.restrictedToken("tools.read(\"src/A.java\")"));
        assertNull(ScriptingTools.restrictedToken("int x = 21; x * 2"));
        assertEquals("ProcessBuilder", ScriptingTools.restrictedToken(
            "new ProcessBuilder(\"ls\").start()"));
        assertEquals("System.exit", ScriptingTools.restrictedToken("System.exit(0)"));
        assertEquals("java.nio.file", ScriptingTools.restrictedToken(
            "java.nio.file.Files.readString(Path.of(\"x\"))"));

        var result = ScriptingTools.run(session, "{\"code\":\"System.exit(0)\"}");
        assertTrue(result.startsWith("[Script rejected by the safety gate"), result);
    }

    @Test
    void unrestrictedModeSkipsTheGate() {
        LlmSettings.INSTANCE.setUnrestrictedExecute(true);
        // 1+1 is harmless; the gate is off, so the snippet evaluates (not just passes the gate)
        assertEquals("2", ScriptingTools.run(session, "{\"code\":\"1+1\"}"));
    }

    @Test
    void runRequiresCode() {
        assertTrue(ScriptingTools.run(session, "{}").startsWith("Error: 'code' parameter"),
            ScriptingTools.run(session, "{}"));
    }

    // ------------------------------------------------------------------ evaluation

    @Test
    void evalReturnsExpressionValuesInOrder() {
        var result = ScriptingTools.eval("int x = 21; x * 2 + 1", facade, 20, 65536);
        assertEquals("43", result);
    }

    @Test
    void evalBindsTheToolsFacade() {
        var result = ScriptingTools.eval("tools != null", facade, 20, 65536);
        assertEquals("true", result);
    }

    @Test
    void facadeCallsDispatchThroughTheSession() {
        // list_tools is GUI-free: its answer proves the dispatch went through the session's
        // real MCP client (routing to the registered tool bodies)
        var result = ScriptingTools.eval("tools.listTools()", facade, 20, 65536);
        assertTrue(result.contains("## Shell"), result);
    }

    @Test
    void facadeShellCallReachesTheShellTool() {
        // a blocked command proves the dispatch went through the real shell tool (blocklist)
        var result = ScriptingTools.eval("tools.shell(\"sudo rm -rf /\")", facade, 20, 65536);
        assertTrue(result.contains("blocked by safety policy"), result);
    }

    @Test
    void evalReportsRejectedSnippetsWithDiagnostics() {
        var result = ScriptingTools.eval("undefinedMethod()", facade, 20, 65536);
        assertTrue(result.startsWith("Error: rejected snippet"), result);
        assertTrue(result.contains("undefinedMethod"), result);
    }

    @Test
    void evalReportsSnippetExceptions() {
        var result = ScriptingTools.eval("tools.call(\"unknown_tool\", \"{}\")", facade, 20,
            65536);
        assertTrue(result.contains("Error: tool unknown_tool failed"), result);
    }

    @Test
    void evalTimesOutAndInterruptsTheSnippet() {
        // sleeps are interrupted by the executor shutdown, so nothing keeps spinning
        var result = ScriptingTools.eval("while (true) { Thread.sleep(10000); }", facade, 1,
            65536);
        assertTrue(result.startsWith("[Script timed out after 1 s"), result);
    }

    @Test
    void evalCapsTheOutput() {
        var result = ScriptingTools.eval("\"y\".repeat(1000)", facade, 20, 50);
        assertEquals(50, result.indexOf("\n... [output truncated at 50 characters]"), result);
    }

    @Test
    void evalReportsNoResultForValuelessSnippets() {
        // a variable declaration yields no expression value
        var result = ScriptingTools.eval("int unusedVariable = 5;", facade, 20, 65536);
        assertTrue(result.startsWith("(no result"), "got: " + result);
    }

    // ------------------------------------------------------------------ metadata

    @Test
    void executeToolMetadata() {
        var tools = new KeYAgentTools();
        var tool = tools.agent(KeYAgentTools.TOOL_EXECUTE);
        assertNotNull(tool, "execute must be registered");
        assertEquals(ToolCategory.SCRIPTING, tool.category());
        assertEquals(Tool.ApprovalRequirement.ASK, tool.approval());
        assertTrue(tool.backgroundable(), "long snippets may run in the background");
        assertTrue(tool.parameters().required().contains("code"));
        var markdown = tool.toMarkdown();
        assertTrue(markdown.contains("`tools`"), markdown);
        assertTrue(markdown.contains("ToolFacade"), markdown);
    }
}
