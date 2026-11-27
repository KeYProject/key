/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.Color;
import java.awt.GraphicsEnvironment;
import java.awt.image.BufferedImage;
import java.util.concurrent.atomic.AtomicReference;
import javax.swing.SwingUtilities;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Tests the Markdown conversion of {@link MarkdownView}: the generated HTML body, the escaping of
 * raw HTML, the GFM extensions, and that a rendered document lays out to its full content height
 * and paints without error.
 */
class MarkdownViewTest {

    /** A document with the constructs that chat answers typically contain. */
    private static final String SAMPLE = """
            ## Proof suggestion

            1. apply the `auto` taclet
            2. **split** the conjunction

            ```java
            int x = 1; // side effect
            ```

            | Taclet | Effect |
            | ------ | ------ |
            | auto   | closes trivial goals |
            | split  | splits conjunctions |

            See [KeY](https://key-project.org) for details. ~~obsolete~~
            """;

    @Test
    void emphasisAndLinksAreRendered() {
        String html = MarkdownView.toHtmlBody("**bold** and *italic*");
        assertEquals("<p><strong>bold</strong> and <em>italic</em></p>\n", html);

        html = MarkdownView.toHtmlBody("see [KeY](https://key-project.org)");
        assertEquals("<p>see <a href=\"https://key-project.org\">KeY</a></p>\n", html);
    }

    @Test
    void rawHtmlIsEscaped() {
        String html = MarkdownView.toHtmlBody("<script>alert(1)</script>");
        assertEquals("<p>&lt;script&gt;alert(1)&lt;/script&gt;</p>\n", html);
    }

    @Test
    void gfmExtensionsAreActive() {
        String html = MarkdownView.toHtmlBody("~~obsolete~~");
        assertEquals("<p><del>obsolete</del></p>\n", html);

        html = MarkdownView.toHtmlBody("| a | b |\n|---|---|\n| 1 | 2 |");
        assertEquals("<table>\n<thead>\n<tr>\n<th>a</th>\n<th>b</th>\n</tr>\n</thead>\n<tbody>\n"
            + "<tr>\n<td>1</td>\n<td>2</td>\n</tr>\n</tbody>\n</table>\n", html);
    }

    @Test
    void fencedCodeBlocksKeepTheirLanguage() {
        String html = MarkdownView.toHtmlBody("```java\nint x = 1;\n```");
        assertEquals("<pre><code class=\"language-java\">int x = 1;\n</code></pre>\n", html);
    }

    @Test
    void documentSizesToContentHeight() throws Exception {
        assumeTrue(!GraphicsEnvironment.isHeadless(), "headless environment");
        var size = new AtomicReference<java.awt.Dimension>();
        SwingUtilities.invokeAndWait(() -> {
            var view = new MarkdownView();
            view.setMarkdown(SAMPLE);
            view.setPreferredWidth(500);
            size.set(view.getPreferredSize());
        });
        // a rich document is much taller than one line, and the forced width is kept
        assertTrue(size.get().height > 100, "content height: " + size.get());
        assertEquals(500, size.get().width);
    }

    @Test
    void documentPaintsWithoutError() throws Exception {
        assumeTrue(!GraphicsEnvironment.isHeadless(), "headless environment");
        var image = new BufferedImage(500, 400, BufferedImage.TYPE_INT_ARGB);
        SwingUtilities.invokeAndWait(() -> {
            var view = new MarkdownView();
            view.setMarkdown(SAMPLE);
            view.setPreferredWidth(500);
            view.setSize(500, 400);
            view.setBackground(Color.ORANGE);
            view.paint(image.getGraphics());
        });
        // the background color of the message box is filled (the document paints on top of it)
        assertEquals(Color.ORANGE.getRGB(), image.getRGB(4, 4));
    }

    @Test
    void changingTheWidthRelayouts() throws Exception {
        assumeTrue(!GraphicsEnvironment.isHeadless(), "headless environment");
        var narrow = new AtomicReference<java.awt.Dimension>();
        var wide = new AtomicReference<java.awt.Dimension>();
        SwingUtilities.invokeAndWait(() -> {
            var view = new MarkdownView();
            view.setMarkdown(SAMPLE);
            view.setPreferredWidth(300);
            narrow.set(view.getPreferredSize());
            view.setPreferredWidth(800);
            wide.set(view.getPreferredSize());
        });
        // at the smaller width the wrapped content needs more vertical space
        assertTrue(narrow.get().height >= wide.get().height,
            "narrow: " + narrow.get() + ", wide: " + wide.get());
    }
}
