/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp;

import java.util.List;

import org.key_project.key.llm.mcp.tools.TestAgentToolProvider;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the modular {@link KeYAgentTools} registry: tools from {@link AgentToolProvider} services
 * are discovered dynamically, the metadata API exposes name/description/parameters/approval, and
 * the self-documenting {@code list_tools} tool dumps all of it as Markdown.
 */
class AgentToolsTest {

    @Test
    void discoversToolsFromAllServiceProviders() {
        var tools = new KeYAgentTools();
        var agents = tools.agents();
        // the built-in set (16 tools) + list_tools + the test provider's tool
        assertTrue(agents.size() >= 18, "expected at least 18 tools, got: " + agents.size());
        for (var name : List.of(KeYAgentTools.TOOL_GET_PROOF_CONTEXT,
            KeYAgentTools.TOOL_LIST_FILES, KeYAgentTools.TOOL_RUN_COMMAND,
            KeYAgentTools.TOOL_ASK_USER, KeYAgentTools.TOOL_TRYCLOSE, KeYAgentTools.TOOL_AUTO,
            KeYAgentTools.TOOL_LIST_PROOFS, KeYAgentTools.TOOL_LIST_TACLETS,
            KeYAgentTools.TOOL_ADD_TACLET, KeYAgentTools.TOOL_LIST_TOOLS,
            TestAgentToolProvider.EXTRA_TOOL)) {
            assertNotNull(tools.agent(name), "tool not discovered: " + name);
        }
    }

    @Test
    void metadataIsAvailableForEveryTool() {
        var tools = new KeYAgentTools();
        for (var agent : tools.agents()) {
            assertTrue(!agent.name().isBlank(), "tool names must not be blank");
            assertTrue(!agent.description().isBlank(),
                "tool " + agent.name() + " must carry a description");
            assertNotNull(agent.parameters(), "tool " + agent.name() + " must have a schema");
            assertNotNull(agent.asTool().function(), "tool " + agent.name()
                + " must serialize to the OpenAI tool format");
        }
        // approval metadata: read-only tools are AUTO, the shell and taclet mutation are ASK
        assertEquals(Tool.ApprovalRequirement.AUTO,
            tools.agent(KeYAgentTools.TOOL_READ_FILE).approval());
        assertEquals(Tool.ApprovalRequirement.ASK,
            tools.agent(KeYAgentTools.TOOL_RUN_COMMAND).approval());
        assertEquals(Tool.ApprovalRequirement.ASK,
            tools.agent(KeYAgentTools.TOOL_ADD_TACLET).approval());
    }

    @Test
    void listToolsDumpsMarkdownDocumentationOfAllTools() throws Exception {
        var tools = new KeYAgentTools();
        var doc = String.valueOf(tools.callTool(KeYAgentTools.TOOL_LIST_TOOLS, "{}"));
        assertTrue(doc.startsWith("# KeY-Agent tools"), "expected a Markdown document:\n" + doc);
        // every tool is documented, with its name, approval and description
        for (var agent : tools.agents()) {
            assertTrue(doc.contains("`" + agent.name() + "`"),
                "documentation must mention tool " + agent.name());
            assertTrue(doc.contains(agent.description()),
                "documentation must carry the description of " + agent.name());
            assertTrue(doc.contains(agent.approval().toString()),
                "documentation must carry the approval of " + agent.name());
        }
        // parameter metadata is rendered for tools that have parameters
        assertTrue(doc.contains("**Parameters:**"), "parameters must be documented");
        assertTrue(doc.contains("`proof`"), "taclet tools must document their proof parameter");
    }

    @Test
    void toolsMarkdownRendersTheSameDocumentation() {
        var tools = new KeYAgentTools();
        assertTrue(tools.toolsMarkdown().contains("### `" + KeYAgentTools.TOOL_READ_FILE + "`"));
        // metadata stays live: the registry snapshot equals the per-tool markdown list
        assertEquals(tools.agents().size(), tools.toolsMarkdown().split("### `").length - 1);
    }

    @Test
    void callToolDispatchesToTheRegisteredAgent() throws Exception {
        var tools = new KeYAgentTools();
        // the test provider's tool is callable through the registry
        var result = String.valueOf(
            tools.callTool(TestAgentToolProvider.EXTRA_TOOL, "{\"x\": \"hello\"}"));
        assertEquals("echo-agent:hello", result);
        assertThrows(IllegalArgumentException.class,
            () -> tools.callTool("no_such_tool", "{}"));
        assertTrue(tools.agents().stream().allMatch(a -> a.asTool().toMap().containsKey("type")));
    }

    @Test
    void selectProofSupportsNameAndIndexIdentifiers() throws Exception {
        var location =
            java.nio.file.Path.of("src/test/resources/org/key_project/key/llm/tacletops.key");
        org.junit.jupiter.api.Assumptions.assumeTrue(java.nio.file.Files.exists(location),
            "File " + location + " not found.");
        de.uka.ilkd.key.control.KeYEnvironment<?> env =
            de.uka.ilkd.key.control.KeYEnvironment.load(location);
        try {
            var proof = env.getLoadedProof();
            var opened = List.of(proof);
            var id = ProofSelector.proofName(proof);
            assertTrue(ProofSelector.selectProof(opened, null, id).proof() == proof,
                "name lookup must resolve the proof");
            assertTrue(ProofSelector.selectProof(opened, null, "0").proof() == proof,
                "index lookup must resolve the proof");
            assertTrue(ProofSelector.selectProof(opened, null, id.toUpperCase()).proof() == proof,
                "name lookup must be case-insensitive");
            assertTrue(ProofSelector.selectProof(opened, null, "1").error() != null,
                "out-of-range index must produce an error");
            assertTrue(ProofSelector.selectProof(opened, null, "absent").error() != null,
                "unknown name must produce an error");
            assertTrue(ProofSelector.proofsBlock(opened, proof).contains(id));
            assertTrue(ProofSelector.proofsBlock(List.of(), null).contains("no proofs"));
        } finally {
            env.dispose();
        }
    }
}
