package de.uka.ilkd.key.gui.interactionlog.model;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.gui.interactionlog.InteractionLogFacade;
import org.key_project.util.collection.ImmutableMapEntry;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;

/**
 * @author weigl
 */
public final class RuleInteraction extends NodeInteraction {

    private String posInOccurence;
    //private NodeIdentifier appliedOn;
    private String ruleName;
    private HashMap<String, String> arguments = new HashMap<>();

    public RuleInteraction() {
        super();
    }

    public RuleInteraction(Node node, RuleApp app) {
        super(node);

        this.ruleName = app.rule().displayName();
        this.posInOccurence = InteractionLogFacade
                .serializePosInOccurence(app.posInOccurrence());

        if (app instanceof TacletApp) {
            TacletApp tapp = (TacletApp) app;
            /*SequentFormula seqForm = pos.getPosInOccurrence().sequentFormula();
            String sfTerm = LogicPrinter.quickPrintTerm(seqForm.formula(), services);
            String onTerm = LogicPrinter.quickPrintTerm(pos.getPosInOccurrence().subTerm(), services);
            sb.append("\n    formula=`").append(sfTerm).append("`");
            sb.append("\n    on=`").append(onTerm).append("`");
            sb.append("\n    occ=?;");
            */
            Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> iter = tapp.instantiations().pairIterator();
            while (iter.hasNext()) {
                ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> entry = iter.next();
                String p = entry.key().toString();

                Object inst = entry.value().getInstantiation();
                String v;

                if (inst instanceof Term) {
                    v = LogicPrinter.quickPrintTerm((Term) inst, null);
                } else {
                    v = inst.toString();
                }

                arguments.put(p, v);
            }
        }
    }

    @Override
    public String toString() {
        return ruleName;
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        return ruleName + ";";
    }

    @Override
    public String getMarkdownText() {
        StringBuilder sb = new StringBuilder();

        sb
            .append("------\n")
            .append("## RuleInteraction ")
            .append(ruleName)
            .append("\n\n")
            .append("### PosInOccurence\n")
            .append("```\n")
            .append(posInOccurence)
            .append("\n```\n\n")
            .append("### arguments:\n")

            .append("| parameter | value |\n")
            .append("| --- | --- |\n");

        arguments.forEach((key, value) -> {
            sb
                .append("| ")
                .append(key)
                .append(" | ")
                .append(value)
                .append(" |")
                .append("\n");
        });


        return sb.toString();
    }

    public String getPosInOccurence() {
        return posInOccurence;
    }

    public void setPosInOccurence(String posInOccurence) {
        this.posInOccurence = posInOccurence;
    }

    public String getRuleName() {
        return ruleName;
    }

    public void setRuleName(String ruleName) {
        this.ruleName = ruleName;
    }

    public HashMap<String, String> getArguments() {
        return arguments;
    }

    public void setArguments(HashMap<String, String> arguments) {
        this.arguments = arguments;
    }
}
