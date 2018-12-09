package de.uka.ilkd.key.gui.interactionlog.algo;

import de.uka.ilkd.key.gui.interactionlog.model.*;
import de.uka.ilkd.key.gui.interactionlog.model.builtin.*;

import java.io.PrintWriter;
import java.io.StringWriter;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
public class MUProofScriptExport extends StreamInteractionVisitor {
    public MUProofScriptExport() {
    }

    public MUProofScriptExport(PrintWriter out) {
        super(out);
    }


    public static String getScriptRepresentation(Interaction interaction) {
        return StreamInteractionVisitor.translate(new MUProofScriptExport(), interaction);
    }

    public static void writeTo(InteractionLog logbook, PrintWriter writer) {
        MUProofScriptExport me = new MUProofScriptExport(writer);
        writer.format("// Proof script: *%s*%n", logbook.getName());
        writer.format("// Created at *%s*%n", logbook.getCreated());
        StreamInteractionVisitor.translate(me, logbook);
    }

    public static String getScript(InteractionLog current) {
        StringWriter sw = new StringWriter();
        writeTo(current, new PrintWriter(sw));
        return sw.toString();
    }


    @Override
    protected Void defaultVisit(Interaction interaction) {
        out.format("// Unsupported interaction: " + interaction.getClass());
        return null;
    }

    @Override
    public Void visit(RuleInteraction interaction) {
        out.format("rule %s;%n", interaction.getRuleName());
        return null;
    }

    @Override
    public Void visit(UseDependencyContractBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(AutoModeInteraction interaction) {
        out.write("auto;%n");
        return null;
    }

    @Override
    public Void visit(MacroInteraction interaction) {
        out.format("macro %s;%n", interaction.getMacro());
        return null;
    }

    @Override
    public Void visit(UserNoteInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(OSSBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(SMTBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(PruneInteraction interaction) {
        out.format("prune %s%n", interaction.getNodeId());
        return null;
    }

    @Override
    public Void visit(LoopContractInternalBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(ContractBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(LoopInvariantBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(SettingChangeInteraction interaction) {
        return super.visit(interaction);
    }

    @Override
    public Void visit(MergeRuleBuiltInRuleInteraction interaction) {
        return super.visit(interaction);
    }
}
