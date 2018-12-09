package de.uka.ilkd.key.gui.interactionlog.algo;

import de.uka.ilkd.key.gui.Markdown;
import de.uka.ilkd.key.gui.interactionlog.model.*;
import de.uka.ilkd.key.gui.interactionlog.model.builtin.OSSBuiltInRuleInteraction;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
public class MarkdownExport extends StreamInteractionVisitor {
    public MarkdownExport() {
    }

    public MarkdownExport(PrintWriter writer) {
        super(writer);
    }

    public static String getMarkdown(Interaction interaction) {
        return StreamInteractionVisitor.translate(new MarkdownExport(), interaction);
    }

    public static void writeTo(InteractionLog logbook, PrintWriter writer) {
        MarkdownExport me = new MarkdownExport(writer);
        writer.format("# Log book *%s*%n%n", logbook.getName());
        writer.format("Created at *%s*%n%n", logbook.getCreated());
        StreamInteractionVisitor.translate(me, logbook);
    }

    public static String getHtml(Interaction inter) {
        return Markdown.html(getMarkdown(inter));
    }

    @Override
    protected Void defaultVisit(Interaction interaction) {
        out.format("**Unsupported interaction: %s**%n%n", interaction.getClass().getName());
        return null;
    }

    @Override
    public Void visit(RuleInteraction interaction) {
        out.format("## Rule applied %s%n%n", interaction.getRuleName());
        out.format("* applied on%s%n", interaction.getPosInOccurence());
        out.format("* Parameters %n");
        interaction.getArguments().forEach((key, value) ->
                out.format("  * %s : %s%n", key, value));
        out.format("%n");
        return null;
    }

    @Override
    public Void visit(AutoModeInteraction interaction) {
        out.write("## Apply auto strategy%n%n");
        out.write("* Started on:");
        interaction.getInitialNodeIds().forEach(nr -> out.format("  * %s%n", nr));
        if (interaction.getOpenGoalNodeIds().isEmpty())
            out.format("* **Closed all goals**");
        else {
            out.format("* finished on:%n");
            interaction.getInitialNodeIds().forEach(nr -> out.format("  * %s%n", nr));
        }
        out.format("```%n%s%n```", interaction.getInfo());
        return null;
    }

    @Override
    public Void visit(MacroInteraction interaction) {
        out.format("## Applied macro %s%n", interaction.getMacro());
        out.format("```%n%s%n```", interaction.getInfo());
        return null;
    }

    @Override
    public Void visit(UserNoteInteraction interaction) {
        out.format("## Note%n");
        out.format("**Date**: %s%n", interaction.getCreated());
        out.format("```%n%s%n```", interaction.getNote());
        return null;
    }

    @Override
    public Void visit(PruneInteraction interaction) {
        out.format("## Prune%n%n");
        out.format("**Date**: %s%n", interaction.getCreated());
        out.format("prune to node %s%n", interaction.getNodeId());
        return null;
    }

    @Override
    public Void visit(SettingChangeInteraction interaction) {
        StringWriter writer = new StringWriter();
        try {
            interaction.getSavedSettings().store(writer, "");
        } catch (IOException e) {
            e.printStackTrace();
        }

        out.format("Setting changed: %s%n", interaction.getType().name());
        out.format("%n```%n%s%n````%n", writer);
        return null;
    }

    @Override
    public Void visit(OSSBuiltInRuleInteraction interaction) {
        out.format("## One step simplification%n");
        out.format("* applied on %n  * Term:%s%n  * Toplevel %s%n",
                interaction.getOccurenceIdentifier().getTerm(),
                interaction.getOccurenceIdentifier().getToplevelTerm());
        return null;
    }
}
