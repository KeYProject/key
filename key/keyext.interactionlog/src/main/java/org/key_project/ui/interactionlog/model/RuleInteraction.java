package org.key_project.ui.interactionlog.model;

import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.RuleCommand;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import org.key_project.util.collection.ImmutableMapEntry;

import javax.xml.bind.annotation.XmlRootElement;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.Iterator;

/**
 * @author weigl
 */
@XmlRootElement
public final class RuleInteraction extends NodeInteraction {
    private static final long serialVersionUID = -3178292652264875668L;
    private String ruleName;
    private OccurenceIdentifier posInOccurence;
    private HashMap<String, String> arguments = new HashMap<>();

    public RuleInteraction() {
        super();
    }

    public RuleInteraction(Node node, RuleApp app) {
        super(node);

        this.ruleName = app.rule().displayName();
        this.posInOccurence = OccurenceIdentifier.get(app.posInOccurrence());

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

    public OccurenceIdentifier getPosInOccurence() {
        return posInOccurence;
    }

    public void setPosInOccurence(OccurenceIdentifier posInOccurence) {
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

    @Override
    public String getMarkdown() {
        StringBuilder out = new StringBuilder();
        out.append(String.format("## Rule applied %s%n%n", getRuleName()));
        out.append(String.format("* applied on%s%n", getPosInOccurence()));
        out.append(String.format("* Parameters %n"));
        getArguments().forEach((key, value) ->
                out.append(String.format("  * %s : %s%n", key, value)));
        out.append('\n');
        return out.toString();
    }

    @Override
    public String getProofScriptRepresentation() {
        StringWriter sout = new StringWriter();
        PrintWriter out = new PrintWriter(sout);

        out.format("rule %s%n", getRuleName());
        out.format("\t     on = \"%s\"%n\tformula = \"%s\"%n",
                getPosInOccurence().getTerm(),
                getPosInOccurence().getToplevelTerm()
        );

        getArguments().forEach((k, v) ->
                out.format("     inst_%s = \"%s\"%n", firstWord(k), v.trim()));
        out.format(";%n");
        return sout.toString();
    }

    private String firstWord(String k) {
        k = k.trim();
        int p = k.indexOf(' ');
        if (p <= 0) return k;
        else return k.substring(0, p);
    }

    @Override
    public void reapply(WindowUserInterfaceControl uic, Goal goal) throws Exception {
        RuleCommand ruleCommand = new RuleCommand();
        EngineState state = new EngineState(goal.proof());
        RuleCommand.Parameters parameter = null;
        try {
            parameter = ruleCommand.evaluateArguments(state, getArguments());
            ruleCommand.execute(uic, parameter, state);
        } catch (Exception e) {
            throw new IllegalStateException("Rule application", e);
        }
    }
}
