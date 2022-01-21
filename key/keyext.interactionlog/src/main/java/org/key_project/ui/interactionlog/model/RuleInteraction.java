package org.key_project.ui.interactionlog.model;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.RuleCommand;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import org.key_project.util.collection.ImmutableMapEntry;

import javax.xml.bind.annotation.XmlRootElement;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;

/**
 * @author weigl
 */
@XmlRootElement
public final class RuleInteraction extends NodeInteraction {
    private static final long serialVersionUID = -3178292652264875668L;
    private static final int indent = 4;
    private final String topLevelTerm;
    private final String subTerm;
    private String ruleName;
    private OccurenceIdentifier posInOccurrence;
    private HashMap<SchemaVariable, String> arguments = new HashMap<>();

    public RuleInteraction(Node node, RuleApp app) {
        super(node);

        this.ruleName = app.rule().displayName();

        var posInOccurrence = app.posInOccurrence();
        if (posInOccurrence == null) {
            this.subTerm = null;
            this.topLevelTerm = null;
        } else {
            var topLevelTerm = posInOccurrence.topLevel().subTerm();
            var subTerm = posInOccurrence.subTerm();
            this.subTerm = subTerm == topLevelTerm || subTerm == null ? null : printTerm(subTerm);
            this.topLevelTerm = printTerm(topLevelTerm);
        }

        this.posInOccurrence = OccurenceIdentifier.get(posInOccurrence);

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
                var p = entry.key();

                Object inst = entry.value().getInstantiation();
                String v;

                if (inst instanceof Term) {
                    v = printTerm((Term) inst);
                } else {
                    v = inst.toString();
                }

                arguments.put(p, v);
            }
        }
    }

    private static String printTerm(Term term) {
        final NotationInfo ni = new NotationInfo();
        LogicPrinter p = new SequentViewLogicPrinter(new ProgramPrinter(), ni, null,
                new TermLabelVisibilityManager());
        p.setLineWidth(100);
        p.reset();

        try {
            p.printTerm(term);
        } catch (IOException ioe) {
            return term.toString();
        }
        return p.result().toString().trim();
    }

    @Override
    public String toString() {
        return ruleName;
    }

    public OccurenceIdentifier getPosInOccurrence() {
        return posInOccurrence;
    }

    public void setPosInOccurrence(OccurenceIdentifier posInOccurrence) {
        this.posInOccurrence = posInOccurrence;
    }

    public String getRuleName() {
        return ruleName;
    }

    public void setRuleName(String ruleName) {
        this.ruleName = ruleName;
    }

    public HashMap<SchemaVariable, String> getArguments() {
        return arguments;
    }

    private HashMap<String, String> createInstArguments() {
        var allArgs = new HashMap<String, String>();
        arguments.forEach((k, v) -> allArgs.put("inst_" + k.name().toString(), v));
        return allArgs;
    }

    private HashMap<String, String> createInvocationArguments() {
        var allArgs = createInstArguments();
        if (topLevelTerm != null) {
            allArgs.put("formula", topLevelTerm);
        }
        if (subTerm != null) {
            allArgs.put("on", subTerm);
        }
        return allArgs;
    }

    @Override
    public String getMarkdown() {
        StringBuilder out = new StringBuilder();
        out.append(String.format("## Rule applied %s%n%n", getRuleName()));
        out.append(String.format("* applied on%s%n", getPosInOccurrence()));
        out.append(String.format("* Parameters %n"));
        getArguments().forEach((key, value) ->
                out.append(String.format("  * %s : %s%n", key, value)));
        out.append('\n');
        return out.toString();
    }

    private static int calculateParameterWidth(Collection<String> args) {
        var width = 0;
        for (var k : args) {
            width = Math.max(k.length(), width);
        }

        return width;
    }

    private static String indentStringWith(String value, String indent) {
        return value.replaceAll("(?m)^", indent);
    }

    @Override
    public String getProofScriptRepresentation() {
        // indent parameters once
        StringWriter sout = new StringWriter();
        PrintWriter out = new PrintWriter(sout);

        out.format("rule %s", getRuleName());

        var args = createInstArguments();
        var width = calculateParameterWidth(args.keySet()) + indent;
        var format = "%n%" + width + "s='%s'";

        // indent inner lines once again
        var innerIndent = " ".repeat(2 + width);

        out.format(format, "formula", indentStringWith(topLevelTerm, innerIndent).trim());
        if (subTerm != null) {
            out.format(format, "on", indentStringWith(subTerm, innerIndent).trim());
        }

        args.forEach((k, v) -> {
            out.format(format, k, indentStringWith(v, innerIndent).trim());
        });

        out.format(";");
        return sout.toString();
    }

    @Override
    public void reapply(WindowUserInterfaceControl uic, Goal goal) {
        RuleCommand ruleCommand = new RuleCommand();
        EngineState state = new EngineState(goal.proof());
        RuleCommand.Parameters parameter;
        try {
            var args = createInvocationArguments();
            args.put("#2", getRuleName());
            parameter = ruleCommand.evaluateArguments(state, args);
            ruleCommand.execute(uic, parameter, state);
        } catch (Exception e) {
            throw new IllegalStateException("Rule application", e);
        }
    }
}
