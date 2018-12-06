package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import org.key_project.util.collection.ImmutableMapEntry;

import java.util.Iterator;

/**
 * @author weigl
 */
public final class RuleInteraction extends NodeInteraction {
    private RuleApp app;
    private String ruleName;

    public RuleInteraction() {
        super(null);
    }

    public RuleInteraction(Node node, RuleApp app) {
        super(node);
        this.app = app;
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        StringBuilder sb = new StringBuilder();
        if (app instanceof TacletApp) {
            TacletApp tapp = (TacletApp) app;
            sb.append(tapp.taclet().name().toString()).append(" ");
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
                String p = "inst_" + entry.key().toString();
                String v = LogicPrinter.quickPrintTerm((Term) entry.value().getInstantiation(), services);
                sb.append("\n    ").append(p).append("=`").append(v).append("`");
            }

            return sb.toString();
        } else {
            return app.toString();
        }
    }

    public RuleApp getApp() {
        return app;
    }
}
