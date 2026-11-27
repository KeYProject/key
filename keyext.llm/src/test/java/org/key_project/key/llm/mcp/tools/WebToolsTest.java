/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.time.Duration;

import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless tests of the web tools: the HTML to Markdown and plain-text conversion, the
 * DuckDuckGo-Lite result parser (both against fixtures), the URL scheme gate and the tool
 * metadata. No network access is performed.
 *
 * @author Alexander Weigl
 */
class WebToolsTest {

    // ------------------------------------------------------------------ html conversion

    @Test
    void toMarkdownConvertsHeadingsLinksListsAndCode() {
        var html = """
                <html><body>
                  <script>evil()</script><style>.x{}</style>
                  <h1>Title</h1>
                  <p>Text with a <a href="https://key-project.org">link</a> and
                     <strong>bold</strong> and <em>italic</em> and <code>code</code>.</p>
                  <ul><li>first</li><li>second</li></ul>
                  <pre><code>int x = 1;</code></pre>
                </body></html>
                """;
        var md = WebTools.toMarkdown(html);
        assertTrue(md.contains("# Title"), md);
        assertTrue(md.contains("[link](https://key-project.org)"), md);
        assertTrue(md.contains("**bold**"), md);
        assertTrue(md.contains("*italic*"), md);
        assertTrue(md.contains("`code`"), md);
        assertTrue(md.contains("- first"), md);
        assertTrue(md.contains("- second"), md);
        assertTrue(md.contains("```\nint x = 1;\n```"), md);
        assertFalse(md.contains("evil"), "scripts must be dropped: " + md);
        assertFalse(md.contains(".x{}"), "styles must be dropped: " + md);
    }

    @Test
    void toMarkdownRendersTables() {
        var html = "<html><body><table><tr><th>Name</th><th>Value</th></tr>"
            + "<tr><td>a</td><td>1</td></tr></table></body></html>";
        var md = WebTools.toMarkdown(html);
        assertTrue(md.contains("| Name | Value |"), md);
        assertTrue(md.contains("| --- | --- |"), md);
        assertTrue(md.contains("| a | 1 |"), md);
    }

    @Test
    void toPlainTextStripsAllMarkup() {
        var html = "<html><body><h1>Head</h1><p>Plain <b>text</b>.</p></body></html>";
        var text = WebTools.toPlainText(html);
        assertTrue(text.contains("Head") && text.contains("Plain text."), text);
        assertFalse(text.contains("<"), text);
        assertFalse(text.contains("h1"), text);
    }

    // ------------------------------------------------------------------ search parsing

    @Test
    void parseSearchResultsReadsDuckDuckGoLiteLayout() {
        var html = """
                <html><body>
                <table>
                  <tr><td>1.&nbsp;</td><td><a rel="nofollow" class="result-link"
                      href="https://key-project.org/doc/">Documentation of KeY</a></td></tr>
                  <tr><td></td><td class="result-snippet">The documentation pages of the KeY
                      system.</td></tr>
                  <tr><td>2.&nbsp;</td><td><a class="result-link"
                      href="https://www.key-project.org/overview">KeY Overview</a></td></tr>
                  <tr><td></td><td class="result-snippet">An overview of deductive verification.
                      </td></tr>
                </table>
                </body></html>
                """;
        var results = WebTools.parseSearchResults(html, 8);
        assertTrue(results.contains("Documentation of KeY"), results);
        assertTrue(results.contains("https://key-project.org/doc/"), results);
        assertTrue(results.contains("The documentation pages of the KeY system."), results);
        assertTrue(results.contains("https://www.key-project.org/overview"), results);
        assertTrue(results.contains("An overview of deductive verification."), results);
        // blocks are separated by blank lines
        assertTrue(results.contains("\n\n"), results);
    }

    @Test
    void parseSearchResultsDropsEndpointNavigationLinks() {
        var html =
            """
                    <html><body>
                      <a href="https://duckduckgo.com/l/?uddg=https%3A%2F%2Fevil.example%2F">redirect</a>
                      <a href="https://example.org/real-result">Real result</a>
                    </body></html>
                    """;
        var results = WebTools.parseSearchResults(html, 8);
        assertTrue(results.contains("example.org/real-result"), results);
        assertFalse(results.contains("duckduckgo.com/l/"), results);
        assertFalse(results.contains("evil.example"), results);
    }

    @Test
    void parseSearchResultsRespectsTheLimit() {
        var sb = new StringBuilder("<html><body>");
        for (int i = 0; i < 20; i++) {
            sb.append("<a href=\"https://example.org/").append(i).append("\">Result ").append(i)
                    .append("</a>");
        }
        sb.append("</body></html>");
        var results = WebTools.parseSearchResults(sb.toString(), 3);
        assertEquals(3, results.split("https://example.org/").length - 1, results);
    }

    @Test
    void parseSearchResultsWithoutMatches() {
        assertEquals("(no results)", WebTools.parseSearchResults("<html><body></body></html>", 8));
    }

    // ------------------------------------------------------------------ url gate + metadata

    @Test
    void webfetchRejectsNonHttpUrls() throws Exception {
        var tools = new KeYAgentTools();
        var tool = tools.agent(KeYAgentTools.TOOL_WEBFETCH);
        var result = tool.call(java.util.Map.of("url", "file:///etc/passwd"));
        assertTrue(result.toString().startsWith("Error: only http and https"), result.toString());
        var ftp = tool.call(java.util.Map.of("url", "ftp://example.org/pub"));
        assertTrue(ftp.toString().startsWith("Error: only http and https"), ftp.toString());
    }

    @Test
    void webfetchRejectsMissingUrlAndUnknownFormats() throws Exception {
        var tools = new KeYAgentTools();
        var tool = tools.agent(KeYAgentTools.TOOL_WEBFETCH);
        assertTrue(tool.call(java.util.Map.of()).toString().contains("'url' parameter"),
            tool.call(java.util.Map.of()).toString());
        // an unknown format is reported without any network access (validation precedes fetch)
        var unknownFormat = tool.call(java.util.Map.of("url", "https://invalid.example.test",
            "format", "yaml"));
        assertTrue(unknownFormat.toString().startsWith("Error: unknown format"),
            unknownFormat.toString());
    }

    @Test
    void websearchRequiresAQuery() throws Exception {
        var tools = new KeYAgentTools();
        var tool = tools.agent(KeYAgentTools.TOOL_WEBSEARCH);
        assertTrue(tool.call(java.util.Map.of()).toString().contains("'query' parameter"),
            tool.call(java.util.Map.of()).toString());
    }

    // ------------------------------------------------------------------ bounded bodies

    @Test
    void readBoundedCapsTheBodyAtTheSizeLimit() throws Exception {
        var big = new byte[WebTools.MAX_BODY_BYTES + 1024];
        try (var stream = new java.io.ByteArrayInputStream(big)) {
            var body = WebTools.readBounded(stream, WebTools.MAX_BODY_BYTES);
            assertEquals(WebTools.MAX_BODY_BYTES, body.bytes().length);
            assertTrue(body.truncated(), "an over-cap body must be reported as truncated");
        }
        try (var stream = new java.io.ByteArrayInputStream(new byte[] { 1, 2, 3 })) {
            var body = WebTools.readBounded(stream, WebTools.MAX_BODY_BYTES);
            assertEquals(3, body.bytes().length);
            assertFalse(body.truncated());
        }
        // a body of exactly the cap is not truncated
        try (var stream = new java.io.ByteArrayInputStream(new byte[WebTools.MAX_BODY_BYTES])) {
            var body = WebTools.readBounded(stream, WebTools.MAX_BODY_BYTES);
            assertEquals(WebTools.MAX_BODY_BYTES, body.bytes().length);
            assertFalse(body.truncated());
        }
    }

    @Test
    void webfetchRejectsResponsesDeclaredLargerThanTheCap() throws Exception {
        var server = com.sun.net.httpserver.HttpServer
                .create(new java.net.InetSocketAddress("127.0.0.1", 0), 0);
        var bodyNeverSent = new java.util.concurrent.CountDownLatch(1);
        server.createContext("/big", exchange -> {
            // the response declares a body far larger than the cap, but never sends it: the
            // pre-check must reject the response from its headers alone (the connection stays
            // open until the test is done, so the client sees a healthy response)
            exchange.sendResponseHeaders(200, WebTools.MAX_BODY_BYTES + 1L);
            try (var out = exchange.getResponseBody()) {
                out.write(1); // force the headers out; the rest of the body is never sent
                out.flush();
                bodyNeverSent.await(30, java.util.concurrent.TimeUnit.SECONDS);
            } catch (InterruptedException ignored) {
                // the test finished
            }
            exchange.close();
        });
        server.start();
        try {
            var tools = new KeYAgentTools();
            var tool = tools.agent(KeYAgentTools.TOOL_WEBFETCH);
            var url = "http://127.0.0.1:" + server.getAddress().getPort() + "/big";
            var result = String.valueOf(tool.call(java.util.Map.of("url", url)));
            assertTrue(result.startsWith("Error: the response is too large"), result);
        } finally {
            bodyNeverSent.countDown();
            server.stop(0);
        }
    }

    @Test
    void webfetchTruncatesUndeclaredOversizedResponses() throws Exception {
        var server = com.sun.net.httpserver.HttpServer
                .create(new java.net.InetSocketAddress("127.0.0.1", 0), 0);
        server.createContext("/liar", exchange -> {
            // chunked (no content-length): the body is larger than the cap
            exchange.sendResponseHeaders(200, 0);
            try (var out = exchange.getResponseBody()) {
                out.write(new byte[WebTools.MAX_BODY_BYTES + 4096]);
            }
        });
        server.start();
        try {
            var tools = new KeYAgentTools();
            var tool = tools.agent(KeYAgentTools.TOOL_WEBFETCH);
            var url = "http://127.0.0.1:" + server.getAddress().getPort() + "/liar";
            var result = assertTimeoutPreemptively(Duration.ofSeconds(30),
                () -> String.valueOf(
                    tool.call(java.util.Map.of("url", url, "format", "text", "timeout", 30))),
                "the bounded drain must stop at the cap instead of buffering everything");
            assertTrue(result.contains("[truncated at 2 MB]"), result);
        } finally {
            server.stop(0);
        }
    }

    @Test
    void webToolsAreStandardAutoAndDocumented() {
        var tools = new KeYAgentTools();
        var webfetch = tools.agent(KeYAgentTools.TOOL_WEBFETCH);
        assertNotNull(webfetch, "webfetch must be registered");
        assertEquals(ToolCategory.WEB, webfetch.category());
        assertEquals(Tool.ApprovalRequirement.AUTO, webfetch.approval());
        assertFalse(webfetch.backgroundable());
        var schema = webfetch.parameters();
        assertNotNull(schema.properties().get("url"));
        assertNotNull(schema.properties().get("format"));
        assertNotNull(schema.properties().get("timeout"));

        var websearch = tools.agent(KeYAgentTools.TOOL_WEBSEARCH);
        assertNotNull(websearch, "websearch must be registered");
        assertEquals(ToolCategory.WEB, websearch.category());
        assertEquals(Tool.ApprovalRequirement.AUTO, websearch.approval());
        assertTrue(websearch.parameters().required().contains("query"));
        assertTrue(webfetch.toMarkdown().contains("2 MB"), webfetch.toMarkdown());
    }
}
