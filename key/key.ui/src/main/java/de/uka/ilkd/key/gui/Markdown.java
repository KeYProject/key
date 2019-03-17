package de.uka.ilkd.key.gui;

import org.commonmark.Extension;
import org.commonmark.ext.gfm.tables.TablesExtension;
import org.commonmark.node.Node;
import org.commonmark.parser.Parser;
import org.commonmark.renderer.html.HtmlRenderer;

import java.util.Arrays;
import java.util.List;

/**
 * A facade to the world of Markdown.
 *
 * @author Alexander Weigl
 * @version 1 (07.12.18)
 */
public class Markdown {
    public static String html(String markdown) {
        List<Extension> extensions = Arrays.asList(TablesExtension.create());
        Parser parser = Parser.builder()
                .extensions(extensions)
                .build();
        HtmlRenderer renderer = HtmlRenderer.builder()
                .extensions(extensions)
                .build();
        Node node = parser.parse(markdown);
        return renderer.render(node);
    }
}
