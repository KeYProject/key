/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.io.IOException;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.StandardCharsets;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;

import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.ToolCategory;

import org.jsoup.Jsoup;
import org.jsoup.nodes.Element;

/**
 * The web tools {@code webfetch} and {@code websearch}: read-only access to public HTTP(S)
 * content. Both run without user approval (AUTO); responses are capped in size and only
 * {@code http} and {@code https} URLs are fetched. {@code webfetch} returns the page as
 * Markdown (default), plain text or raw HTML ({@link org.jsoup} converts); {@code websearch}
 * queries the configured HTML search endpoint (default: DuckDuckGo Lite, no API key needed)
 * and reports the result links with titles and snippets.
 *
 * @author Alexander Weigl
 */
public final class WebTools implements AgentToolProvider {

    /** The hard cap of a fetched document body (2 MiB). */
    static final int MAX_BODY_BYTES = 2 * 1024 * 1024;

    /** The maximum number of search results reported. */
    static final int MAX_SEARCH_RESULTS = 8;

    /** The shared, connection-pooling client of all web tools. */
    private static final HttpClient CLIENT = HttpClient.newBuilder()
            .followRedirects(HttpClient.Redirect.NORMAL).connectTimeout(Duration.ofSeconds(15))
            .build();

    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(KeYAgentTools.TOOL_WEBFETCH, ToolCategory.WEB,
                "Fetches a web page (http/https only) and returns its content as"
                    + " Markdown (default), plain text or raw HTML. Responses are capped at"
                    + " 2 MB. No authentication and no cookies are sent; there is no address"
                    + " restriction beyond the http/https scheme - local and internal network"
                    + " addresses are reachable like any public site, so only fetch URLs whose"
                    + " content you intend to bring into the conversation.",
                AgentTool.schema("url",
                    JsonSchema.builder().withType("string")
                            .withDescription("the http(s) URL to fetch").build(),
                    "format",
                    JsonSchema.builder().withType("string")
                            .withDescription("output format: \"markdown\" (default),"
                                + " \"text\" or \"html\"")
                            .withEnum(List.of("markdown", "text", "html")).build(),
                    "timeout",
                    JsonSchema.builder().withType("integer")
                            .withDescription("request timeout in seconds (default 30,"
                                + " at most 120)")
                            .build()),
                args -> webfetch(AgentTool.stringArg(args, "url"),
                    AgentTool.stringArg(args, "format"), AgentTool.intArg(args, "timeout"))),
            AgentTool.tool(KeYAgentTools.TOOL_WEBSEARCH, ToolCategory.WEB,
                "Searches the web with the configured HTML search endpoint (default:"
                    + " DuckDuckGo Lite, no API key) and reports up to 8 results as"
                    + " \"title\\nURL\\nsnippet\" blocks. Use for documentation, papers and"
                    + " error messages; then fetch the promising pages with webfetch.",
                JsonSchema.builder().withType("object")
                        .addProperty("query",
                            JsonSchema.builder().withType("string")
                                    .withDescription("the search query").build())
                        .withRequired(List.of("query"))
                        .build(),
                args -> websearch(AgentTool.stringArg(args, "query"))));
    }

    // --------------------------------------------------------------------------- webfetch

    /** The {@code webfetch} body: validates the URL and format, fetches and converts. */
    private static String webfetch(String url, String format, Integer timeoutSeconds) {
        if (url == null || url.isBlank()) {
            return "Error: 'url' parameter is required";
        }
        URI uri;
        try {
            uri = URI.create(url.strip());
        } catch (IllegalArgumentException e) {
            return "Error: invalid URL \"" + url + "\": " + e.getMessage();
        }
        var scheme = uri.getScheme() == null ? "" : uri.getScheme().toLowerCase();
        if (!scheme.equals("http") && !scheme.equals("https")) {
            return "Error: only http and https URLs are fetched: " + url;
        }
        var outputFormat = format == null || format.isBlank() ? "markdown" : format.strip();
        if (!outputFormat.equals("markdown") && !outputFormat.equals("text")
                && !outputFormat.equals("html")) {
            return "Error: unknown format \"" + outputFormat
                + "\" (use \"markdown\", \"text\" or \"html\")";
        }
        int timeout = timeoutSeconds == null ? 30 : Math.max(1, Math.min(timeoutSeconds, 120));
        var request = HttpRequest.newBuilder(uri).timeout(Duration.ofSeconds(timeout))
                .header("Accept", "text/html,application/xhtml+xml,text/plain;q=0.8,*/*;q=0.5")
                .header("User-Agent", "KeY-Agent/1.0 (+https://key-project.org)").GET().build();
        HttpResponse<java.io.InputStream> response;
        try {
            response = CLIENT.send(request, HttpResponse.BodyHandlers.ofInputStream());
        } catch (IOException e) {
            return "Error: fetch failed: " + e.getMessage();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return "Error: fetch interrupted";
        }
        try (var body = response.body()) {
            int status = response.statusCode();
            if (status >= 400) {
                return "Error: the server answered with HTTP status " + status + " for " + url;
            }
            // the memory cap is enforced while reading: an oversized *declared* body is not
            // downloaded at all, and an undeclared or undersold body is drained at most to
            // the cap (the connection is closed instead)
            long declared = response.headers().firstValueAsLong("content-length").orElse(-1);
            if (declared > MAX_BODY_BYTES) {
                return "Error: the response is too large (" + declared + " bytes; the cap is "
                    + MAX_BODY_BYTES + " bytes): " + url;
            }
            var bounded = readBounded(body, MAX_BODY_BYTES);
            var text = new String(bounded.bytes(), StandardCharsets.UTF_8);
            var mime = response.headers().firstValue("content-type").orElse("");
            return switch (outputFormat) {
                case "html" -> cap(text, bounded.truncated());
                case "text" ->
                    cap(mime.contains("html") ? toPlainText(text) : text.stripTrailing(),
                        bounded.truncated());
                default -> cap(mime.contains("html") ? toMarkdown(text) : text.stripTrailing(),
                    bounded.truncated());
            };
        } catch (IOException e) {
            return "Error: the response could not be read: " + e.getMessage();
        }
    }

    /**
     * One bounded response body: at most {@code maxBytes} raw bytes, and whether the stream had
     * more.
     */
    record BoundedBody(byte[] bytes, boolean truncated) {
    }

    /**
     * Reads at most {@code maxBytes} bytes from the stream; reports whether more was
     * available. Bounded in memory: nothing beyond the cap is buffered (the caller closes the
     * stream instead of draining it). Package-private so the boundedness can be tested
     * headless.
     */
    static BoundedBody readBounded(java.io.InputStream stream, int maxBytes) throws IOException {
        var out = new java.io.ByteArrayOutputStream(Math.min(maxBytes, 64 * 1024));
        var buffer = new byte[8192];
        boolean truncated = false;
        int read;
        while ((read = stream.read(buffer)) >= 0) {
            int room = maxBytes - out.size();
            if (room <= 0) {
                truncated = true;
                break;
            }
            if (read > room) {
                truncated = true;
            }
            out.write(buffer, 0, Math.min(room, read));
        }
        return new BoundedBody(out.toByteArray(), truncated);
    }

    /** Appends a truncation note to a body that was cut at the size cap. */
    private static String cap(String text, boolean truncated) {
        return truncated ? text.stripTrailing() + "\n... [truncated at 2 MB]"
                : text.stripTrailing();
    }

    // --------------------------------------------------------------------------- converters

    /**
     * Converts an HTML document to compact Markdown: headings, paragraphs, lists, links,
     * emphasis, code blocks; scripts, styles and navigation noise are dropped. Package-private
     * so the conversion can be tested headless.
     */
    static String toMarkdown(String html) {
        var document = Jsoup.parse(html);
        document.select("script, style, noscript, nav, header, footer, aside, form, iframe")
                .remove();
        var md = new StringBuilder();
        appendMarkdown(document.body(), md);
        var text = md.toString().replaceAll("\n{3,}", "\n\n").strip();
        return text + (html.length() > MAX_BODY_BYTES ? "\n... [truncated at 2 MB]" : "");
    }

    /** The plain-text extraction of an HTML document (same noise removal as Markdown). */
    static String toPlainText(String html) {
        var document = Jsoup.parse(html);
        document.select("script, style, noscript, nav, header, footer, aside, form, iframe")
                .remove();
        var text = document.body() == null ? "" : document.body().wholeText();
        return text.replaceAll("\n{3,}", "\n\n").strip();
    }

    /** Appends {@code element} as Markdown to {@code md}. */
    private static void appendMarkdown(Element element, StringBuilder md) {
        for (var node : element.childNodes()) {
            if (node instanceof org.jsoup.nodes.TextNode t) {
                var text = t.text();
                if (!text.isBlank()) {
                    md.append(text).append(' ');
                }
                continue;
            }
            if (!(node instanceof Element child)) {
                continue;
            }
            var tag = child.tagName().toLowerCase();
            switch (tag) {
                case "h1", "h2", "h3", "h4", "h5", "h6" -> {
                    var level = tag.charAt(1) - '0';
                    md.append("\n\n").append("#".repeat(level)).append(' ')
                            .append(child.text().strip()).append("\n\n");
                }
                case "p", "section", "article", "div", "blockquote", "figcaption" -> {
                    appendMarkdown(child, md);
                    md.append("\n\n");
                }
                case "br" -> md.append('\n');
                case "li" -> {
                    md.append("- ").append(child.text().strip()).append('\n');
                }
                case "ul", "ol" -> {
                    appendMarkdown(child, md);
                    md.append('\n');
                }
                case "a" -> {
                    var href = child.attr("href");
                    var label = child.text().strip();
                    if (href.isBlank() || label.isBlank()) {
                        md.append(label);
                    } else if (href.startsWith("#")) {
                        md.append(label); // in-page anchors are noise in Markdown
                    } else {
                        md.append('[').append(label).append(']').append('(').append(href)
                                .append(')');
                    }
                    md.append(' ');
                }
                case "code" -> {
                    if (child.parent() != null && "pre".equals(child.parent().tagName())) {
                        break; // handled by pre
                    }
                    md.append('`').append(child.text().strip()).append('`').append(' ');
                }
                case "pre" -> {
                    md.append("\n\n```\n").append(child.text().strip()).append("\n```\n\n");
                }
                case "em", "i" -> md.append('*').append(child.text().strip()).append("* ");
                case "strong", "b" -> md.append("**").append(child.text().strip()).append("** ");
                case "img" -> {
                    var alt = child.attr("alt");
                    if (!alt.isBlank()) {
                        md.append('[').append(alt).append(" image] ");
                    }
                }
                case "table" -> {
                    appendTable(child, md);
                }
                case "hr" -> md.append("\n\n---\n\n");
                case "dl", "dt", "dd", "span", "small", "sup", "sub" -> appendMarkdown(child, md);
                default -> appendMarkdown(child, md);
            }
        }
    }

    /** Appends a simple two-row Markdown table (header row plus body rows). */
    private static void appendTable(Element table, StringBuilder md) {
        var rows = table.select("tr");
        if (rows.isEmpty()) {
            md.append('\n');
            return;
        }
        for (int i = 0; i < Math.min(rows.size(), 20); i++) {
            var cells = rows.get(i).select("th, td");
            var line = new ArrayList<String>();
            for (var cell : cells) {
                line.add(cell.text().strip());
            }
            md.append("| ").append(String.join(" | ", line)).append(" |\n");
            if (i == 0) {
                md.append("|").append(" --- |".repeat(Math.max(1, line.size()))).append('\n');
            }
        }
        md.append('\n');
    }

    // --------------------------------------------------------------------------- websearch

    /** The {@code websearch} body: queries the configured endpoint and parses the results. */
    private static String websearch(String query) {
        if (query == null || query.isBlank()) {
            return "Error: 'query' parameter is required";
        }
        var endpoint = LlmSettings.INSTANCE.getWebSearchEndpoint();
        URI uri;
        try {
            var separator = endpoint.contains("?") ? "&" : "?";
            uri = URI.create(endpoint + separator + "q="
                + java.net.URLEncoder.encode(query, StandardCharsets.UTF_8));
        } catch (IllegalArgumentException e) {
            return "Error: invalid web search endpoint \"" + endpoint + "\": " + e.getMessage();
        }
        var request = HttpRequest.newBuilder(uri).timeout(Duration.ofSeconds(30))
                .header("User-Agent", "KeY-Agent/1.0 (+https://key-project.org)")
                .header("Accept", "text/html").GET().build();
        HttpResponse<String> response;
        try {
            response = CLIENT.send(request, HttpResponse.BodyHandlers.ofString());
        } catch (IOException e) {
            return "Error: web search failed: " + e.getMessage();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return "Error: web search interrupted";
        }
        if (response.statusCode() >= 400) {
            return "Error: the search endpoint answered with HTTP status " + response.statusCode();
        }
        return parseSearchResults(response.body(), MAX_SEARCH_RESULTS);
    }

    /**
     * Parses the HTML of a DuckDuckGo-Lite-style result page into
     * "{@code title\nURL\nsnippet}" blocks separated by blank lines. Package-private so the
     * parser can be tested with a fixture. Unknown markup degrades to the links it can find.
     */
    static String parseSearchResults(String html, int limit) {
        var document = Jsoup.parse(html);
        var results = new ArrayList<String>();
        var links = document.select("a.result-link, a.result__a, a[href^='http']");
        for (var link : links) {
            if (results.size() >= limit) {
                break;
            }
            var url = link.absUrl("href");
            if (url.isBlank()) {
                url = link.attr("href");
            }
            if (url.isBlank()) {
                continue;
            }
            if (url.startsWith("https://duckduckgo.com/l/") || url.contains("duckduckgo.com")) {
                continue; // the endpoint's own navigation links
            }
            var title = link.text().strip();
            // the snippet is the following paragraph/sibling in DuckDuckGo Lite's table layout
            var snippet = snippetOf(link);
            results.add(title + "\n" + url + (snippet.isEmpty() ? "" : "\n" + snippet));
        }
        if (results.isEmpty()) {
            return "(no results)";
        }
        return String.join("\n\n", results);
    }

    /**
     * The snippet text of a result link: the next non-empty cell of the link's row, then the
     * row after it (DuckDuckGo Lite renders one row per result and one per snippet), then the
     * next sibling block of the link's container.
     */
    private static String snippetOf(Element link) {
        var cell = link.closest("td");
        if (cell != null) {
            var next = cell.nextElementSibling();
            while (next != null) {
                var text = next.text().strip();
                if (!text.isEmpty()) {
                    return text;
                }
                next = next.nextElementSibling();
            }
            var row = link.closest("tr");
            if (row != null && row.nextElementSibling() != null
                    && !row.nextElementSibling().text().isBlank()) {
                return row.nextElementSibling().text().strip();
            }
        }
        var parent = link.parent();
        var next = parent == null ? null : parent.nextElementSibling();
        while (next != null) {
            var text = next.text().strip();
            if (!text.isEmpty()) {
                return text;
            }
            next = next.nextElementSibling();
        }
        return "";
    }
}
