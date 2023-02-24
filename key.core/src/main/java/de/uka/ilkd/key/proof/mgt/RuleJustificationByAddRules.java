package de.uka.ilkd.key.proof.mgt;


import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;


public class RuleJustificationByAddRules implements RuleJustification {

    private final Node node;
    private final boolean isAxiom;

    public RuleJustificationByAddRules(Node node, boolean isAxiom) {
        assert node != null;
        this.node = node;
        this.isAxiom = isAxiom;
    }

    public boolean isAxiomJustification() {
        return isAxiom;
    }

    public RuleApp motherTaclet() {
        return node.getAppliedRuleApp();
    }

    public String toString() {
        String mother;
        if (motherTaclet().rule() instanceof Taclet) {
            LogicPrinter tacPrinter = new LogicPrinter(new ProgramPrinter(null), new NotationInfo(),
                node.proof().getServices(), true);
            tacPrinter.printTaclet((Taclet) (motherTaclet().rule()));
            mother = tacPrinter.toString();
        } else {
            mother = motherTaclet().rule().name().toString();
        }
        return "added rule justification \nintroduced at node " + node.serialNr() + " by rule \n"
            + mother;
    }
}
