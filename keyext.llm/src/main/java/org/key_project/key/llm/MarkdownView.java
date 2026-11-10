/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Desktop;
import java.awt.Dimension;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.image.BufferedImage;
import java.io.InputStream;
import java.io.StringReader;
import java.net.URI;
import java.util.List;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.SwingUtilities;

import org.commonmark.Extension;
import org.commonmark.ext.gfm.strikethrough.StrikethroughExtension;
import org.commonmark.ext.gfm.tables.TablesExtension;
import org.commonmark.node.Node;
import org.commonmark.parser.Parser;
import org.commonmark.renderer.html.HtmlRenderer;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xhtmlrenderer.resource.CSSResource;
import org.xhtmlrenderer.resource.ImageResource;
import org.xhtmlrenderer.resource.XMLResource;
import org.xhtmlrenderer.simple.XHTMLPanel;
import org.xhtmlrenderer.simple.extend.XhtmlNamespaceHandler;
import org.xhtmlrenderer.swing.LinkListener;
import org.xhtmlrenderer.swing.NaiveUserAgent;

/**
 * Renders a Markdown message (an agent answer) as rich HTML text.
 * <p>
 * The Markdown is parsed with
 * <a href="https://github.com/commonmark/commonmark-java">commonmark-java</a>
 * (GFM tables and strikethrough enabled, raw HTML escaped) and rendered with
 * <a href="https://github.com/flyingsaucerproject/flyingsaucer">FlyingSaucer</a>
 * ({@link XHTMLPanel}), which gives proper headings, lists, code blocks, tables and
 * block quotes. The view embeds the HTML panel without a scroll pane: it sizes itself to
 * the full content height at the available width, so the conversation's own scroll pane
 * handles the scrolling.
 * <p>
 * Rendering is strictly offline: the embedded user agent denies every external resource
 * (images, stylesheets, documents), so nothing is fetched from the network; http(s) links
 * are opened in the system browser on click instead.
 *
 * @author Alexander Weigl
 */
public class MarkdownView extends JPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(MarkdownView.class);

    /** The CSS of the rendered message; the base font is inherited from the Swing component. */
    private static final String STYLE = """
            body { margin: 0; }
            p { margin: 0 0 4px 0; }
            h1, h2, h3, h4, h5, h6 { margin: 8px 0 4px 0; font-weight: bold; }
            h1 { font-size: 1.4em; } h2 { font-size: 1.25em; } h3 { font-size: 1.12em; }
            ul, ol { margin: 2px 0 4px 0; padding-left: 18px; }
            li { margin: 1px 0; }
            pre { background-color: #eef1f4; padding: 4px 6px; margin: 4px 0;
                  font-family: 'Monospaced', monospace; font-size: 0.92em;
                  white-space: pre-wrap; }
            code { font-family: 'Monospaced', monospace; font-size: 0.92em; }
            blockquote { margin: 4px 0 4px 8px; padding-left: 8px;
                         border-left: 3px solid #b0b8c0; font-style: italic; }
            table { border-collapse: collapse; margin: 4px 0; }
            th, td { border: 1px solid #b0b8c0; padding: 2px 6px; }
            th { background-color: #e4e8ec; text-align: left; }
            hr { border: none; border-top: 1px solid #b0b8c0; margin: 6px 0; }
            a { color: #0645ad; }""";

    /** The fallback width when the view is not (yet) inside the conversation layout. */
    private static final int DEFAULT_WIDTH = 480;

    /** The GFM extensions that chat models typically emit. */
    private static final List<Extension> EXTENSIONS =
        List.of(TablesExtension.create(), StrikethroughExtension.create());

    /** CommonMark parser with the GFM extensions. */
    private static final Parser PARSER = Parser.builder().extensions(EXTENSIONS).build();

    /** HTML renderer that escapes raw HTML so model output cannot inject markup. */
    private static final HtmlRenderer RENDERER =
        HtmlRenderer.builder().escapeHtml(true).extensions(EXTENSIONS).build();

    /** The rendered document. */
    private final XHTMLPanel html = new XHTMLPanel(new OfflineUserAgent());
    /** The width the current cached size was computed for ({@code -1} = stale). */
    private int cachedWidth = -1;
    /** The preferred size at {@link #cachedWidth}; {@code null} when stale. */
    private @Nullable Dimension cachedSize;
    /** A forced layout width ({@code 0} = derive from the conversation width); used by tests. */
    private int overrideWidth;

    public MarkdownView() {
        super(new BorderLayout());

        // inherit the KeY UI font as the document default; the background is kept on the Swing
        // panels (the document body stays transparent) so message box colors show through
        html.setDefaultFontFromComponent(true);
        // follow links in the system browser instead of navigating the embedded panel
        for (var listener : html.getMouseTrackingListeners()) {
            if (listener instanceof LinkListener) {
                html.removeMouseTrackingListener(listener);
            }
        }
        html.addMouseListener(new LinkOpener());
        add(html, BorderLayout.CENTER);
    }

    /** Shows the given Markdown text, rendered as HTML. */
    public void setMarkdown(String markdown) {
        setHtml(toHtmlBody(markdown));
    }

    /** Shows the given HTML body fragment (as produced by the Markdown conversion). */
    public void setHtml(String body) {
        html.setDocumentFromString(
            "<html><head><style>" + STYLE + "</style></head><body>" + body + "</body></html>",
            null, new XhtmlNamespaceHandler());
        cachedSize = null;
        cachedWidth = -1;
        revalidate();
        repaint();
    }

    /** Forces the layout width; {@code 0} (the default) derives it from the conversation. */
    void setPreferredWidth(int width) {
        overrideWidth = Math.max(0, width);
        cachedSize = null;
        cachedWidth = -1;
        revalidate();
        repaint();
    }

    @Override
    public void setBackground(Color bg) {
        super.setBackground(bg);
        // JPanel's constructor installs the look&feel colors before the field initializers have
        // run; also the document paints on top of the panel background (its body has no
        // background-color), so the message box color is filled by Swing before the HTML is
        // painted
        if (html != null) {
            html.setBackground(bg);
        }
    }

    @Override
    public Dimension getPreferredSize() {
        int width = availableWidth();
        if (cachedSize == null || cachedWidth != width) {
            cachedWidth = width;
            cachedSize = layoutContent(width);
        }
        return new Dimension(cachedSize);
    }

    /** The width the document is laid out at: this view's actual width in the conversation. */
    private int availableWidth() {
        if (overrideWidth > 0) {
            return overrideWidth;
        }
        // the exact width: the one the surrounding layout last gave us (includes the insets of
        // the message box and of the layout manager in between, whatever they are)
        if (getWidth() > 0) {
            return getWidth();
        }
        // before the first layout we only have the enclosing viewport; the borders of the
        // components in between (the message box) reduce the width available to the document
        if (SwingUtilities.getAncestorOfClass(JScrollPane.class,
            this) instanceof JScrollPane pane) {
            int width = pane.getViewportBorderBounds().width;
            for (var c = (java.awt.Container) this; c != null && c != pane; c = c.getParent()) {
                var insets = c.getInsets();
                width -= insets.left + insets.right;
            }
            if (width > 0) {
                return width;
            }
        }
        return DEFAULT_WIDTH;
    }

    @Override
    public void setBounds(int x, int y, int width, int height) {
        boolean widthChanged = width > 0 && width != getWidth();
        super.setBounds(x, y, width, height);
        if (widthChanged && overrideWidth == 0) {
            // the height was computed for the previous width; schedule a layout at the new width
            cachedSize = null;
            cachedWidth = -1;
            revalidate();
        }
    }

    /**
     * Lays the document out at the given width and returns the required height. FlyingSaucer
     * computes the content height during layout, which otherwise happens lazily on the first
     * paint; forcing it here lets the surrounding layout manager (which relies on the preferred
     * size) give the view its full height right away.
     */
    private Dimension layoutContent(int width) {
        if (html.getDocument() == null) {
            return new Dimension(width, 10);
        }
        // a throw-away graphics is enough: the layout only reads font metrics from it
        var image = new BufferedImage(1, 1, BufferedImage.TYPE_INT_ARGB);
        var graphics = image.createGraphics();
        try {
            html.setSize(width, 100);
            html.doDocumentLayout(graphics);
        } finally {
            graphics.dispose();
        }
        // after the layout, the panel reports the content height as its preferred size
        int height = Math.max(10, html.getPreferredSize().height);
        html.setSize(width, height);
        return new Dimension(width, height);
    }

    /** Converts Markdown to an HTML body fragment: raw HTML is escaped, GFM tables supported. */
    static String toHtmlBody(String markdown) {
        Node document = PARSER.parse(markdown);
        return RENDERER.render(document);
    }

    /**
     * A user agent that denies every remote resource: the HTML comes from the model, so images,
     * stylesheets and documents are never fetched from the network. Only local resources are
     * allowed past this filter: {@code data:} URIs (which fail at the JDK level anyway) and
     * {@code jar:}/{@code file:} URLs, from which FlyingSaucer loads its built-in default
     * stylesheet. Denied image loads degrade to FlyingSaucer's built-in broken-image handling.
     */
    private static final class OfflineUserAgent extends NaiveUserAgent {
        private static boolean isLocal(@Nullable String uri) {
            return uri != null && (uri.startsWith("jar:") || uri.startsWith("file:")
                    || uri.startsWith("data:"));
        }

        @Override
        protected @Nullable InputStream resolveAndOpenStream(@Nullable String uri) {
            // also backs getCSSResource, getXMLResource and getBinaryResource, and (for
            // FlyingSaucer's own default stylesheet) stylesheet loading in general
            return isLocal(uri) ? super.resolveAndOpenStream(uri) : null;
        }

        @Override
        public CSSResource getCSSResource(String uri) {
            // stylesheets cannot be referenced through the escaped HTML, but the built-in
            // default stylesheet must resolve
            return isLocal(uri) ? super.getCSSResource(uri) : new CSSResource(null);
        }

        @Override
        public XMLResource getXMLResource(String uri) {
            return isLocal(uri) ? super.getXMLResource(uri)
                    : XMLResource.load(new StringReader(""));
        }

        @Override
        public ImageResource getImageResource(String imageLocation) {
            if (isLocal(imageLocation)) {
                return super.getImageResource(imageLocation);
            }
            return createImageResource(imageLocation, null);
        }
    }

    /** Opens http(s) links of the rendered document in the system browser. */
    private static final class LinkOpener extends MouseAdapter {
        @Override
        public void mouseClicked(MouseEvent e) {
            if (!(e.getComponent() instanceof XHTMLPanel panel)) {
                return;
            }
            var box = panel.find(e.getX(), e.getY());
            while (box != null) {
                var element = box.getElement();
                if (element != null && element.hasAttribute("href")) {
                    openExternally(element.getAttribute("href"));
                    return;
                }
                box = box.getParent();
            }
        }

        private void openExternally(String href) {
            if (!href.startsWith("http://") && !href.startsWith("https://")) {
                return;
            }
            var desktop = Desktop.getDesktop();
            if (!Desktop.isDesktopSupported() || !desktop.isSupported(Desktop.Action.BROWSE)) {
                LOGGER.info("Link {} cannot be opened (no desktop integration)", href);
                return;
            }
            try {
                desktop.browse(URI.create(href));
            } catch (Exception ex) {
                LOGGER.warn("Could not open link {}", href, ex);
            }
        }
    }
}
