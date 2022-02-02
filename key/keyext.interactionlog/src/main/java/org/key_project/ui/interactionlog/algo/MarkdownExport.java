package org.key_project.ui.interactionlog.algo;

import org.key_project.ui.interactionlog.api.Markdownable;
import org.key_project.ui.interactionlog.api.Interaction;
import org.key_project.ui.interactionlog.model.InteractionLog;
import org.key_project.ui.markdown.Markdown;

import java.io.PrintWriter;

public class MarkdownExport {
    private final PrintWriter writer;

    public MarkdownExport(PrintWriter writer) {
        this.writer = writer;
    }

    public static void writeTo(InteractionLog logbook, PrintWriter writer) {
        MarkdownExport me = new MarkdownExport(writer);
        writer.format("# Log book *%s*%n%n", logbook.getName());
        writer.format("Created at *%s*%n%n", logbook.getCreated());
        logbook.getInteractions().forEach(it -> writer.format(getMarkdown(it) + "\n"));
    }

    public static String getMarkdown(Interaction interaction) {
        try {
            Markdownable m = (Markdownable) interaction;
            return m.getMarkdown();
        } catch (ClassCastException e) {
        }
        return "";
    }

    public static String getHtml(Interaction inter) {
        return Markdown.html(getMarkdown(inter));
    }
}
