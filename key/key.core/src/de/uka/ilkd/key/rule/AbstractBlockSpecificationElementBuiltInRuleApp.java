package de.uka.ilkd.key.rule;

import java.util.List;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.BlockSpecificationElement;

public abstract class AbstractBlockSpecificationElementBuiltInRuleApp
        extends AbstractBuiltInRuleApp {

    protected StatementBlock block;
    protected List<LocationVariable> heaps;
    protected IFProofObligationVars infFlowVars;
    protected ExecutionContext context;

    public AbstractBlockSpecificationElementBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence occurrence,
            ImmutableList<PosInOccurrence> ifInstantiations) {
        super(rule, occurrence, ifInstantiations);
    }

    public StatementBlock getBlock() {
        return block;
    }

    public abstract BlockSpecificationElement getContract();

    public IFProofObligationVars getInformationFlowProofObligationVars() {
        return infFlowVars;
    }

    public ExecutionContext getExecutionContext() {
        return context;
    }

    @Override
    public List<LocationVariable> getHeapContext() {
        return heaps;
    }

    @Override
    public boolean complete() {
        return pio != null && block != null && getContract() != null && heaps != null;
    }

    @Override
    public boolean isSufficientlyComplete() {
        return pio != null;
    }

    public boolean cannotComplete(final Goal goal) {
        return !builtInRule.isApplicable(goal, pio);
    }

    public void update(IFProofObligationVars vars, ExecutionContext context) {
        this.infFlowVars = vars;
        this.context = context;
    }
}
