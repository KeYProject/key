package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import org.key_project.util.collection.ImmutableMapEntry;

import java.util.HashMap;
import java.util.Iterator;

/**
 * @author weigl
 */
public final class RuleInteraction extends NodeInteraction {
    private PosInOccurrence posInOccurence;
    //private NodeIdentifier appliedOn;
    private String ruleName;
    private HashMap<String, String> arguments = new HashMap<>();

    public RuleInteraction() {
        super((NodeIdentifier) null);
    }

    public RuleInteraction(Node node, RuleApp app) {
        super(NodeIdentifier.get(node));

        this.ruleName = app.rule().displayName();
        this.posInOccurence = app.posInOccurrence();

        StringBuilder sb = new StringBuilder();
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
                String v = LogicPrinter.quickPrintTerm((Term) entry.value().getInstantiation(), null);
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
        return "";
    }

    public String getRuleName() {
        return ruleName;
    }

    public void setRuleName(String ruleName) {
        this.ruleName = ruleName;
    }

    public PosInOccurrence getPosInOccurence() {
        return posInOccurence;
    }

    public void setPosInOccurence(PosInOccurrence posInOccurence) {
        this.posInOccurence = posInOccurence;
    }
}
