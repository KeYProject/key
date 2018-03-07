package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.informationflow.po.SymbolicExecutionPO;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.LoopContract;

/**
 * <p>Rule for the application of {@link LoopContract}s.</p>
 * 
 * @see AbstractLoopContractBuiltInRuleApp
 */
public abstract class AbstractLoopContractRule extends AbstractBlockSpecificationElementRule {

    public static ImmutableSet<LoopContract> getApplicableContracts(final Instantiation instantiation,
                                                                     final Goal goal,
                                                                     final Services services) {
        if (instantiation == null) {
            return DefaultImmutableSet.nil();
        }
        return getApplicableContracts(services.getSpecificationRepository(),
                                      instantiation.block,
                                      instantiation.modality, goal);
    }

    public static ImmutableSet<LoopContract>
                        getApplicableContracts(final SpecificationRepository specifications,
                                               final StatementBlock block,
                                               final Modality modality,
                                               final Goal goal) {
        ImmutableSet<LoopContract> collectedContracts =
                specifications.getLoopContracts(block, modality);
        if (modality == Modality.BOX) {
            collectedContracts = collectedContracts.union(
                    specifications.getLoopContracts(block, Modality.DIA));
        }
        else if (modality == Modality.BOX_TRANSACTION) {
            collectedContracts = collectedContracts.union(
                    specifications.getLoopContracts(block, Modality.DIA_TRANSACTION));
        }
        return filterAppliedContracts(collectedContracts, goal);
    }

    protected static ImmutableSet<LoopContract>
                        filterAppliedContracts(final ImmutableSet<LoopContract> collectedContracts,
                                               final Goal goal) {
        ImmutableSet<LoopContract> result = DefaultImmutableSet.<LoopContract>nil();
        for (LoopContract contract : collectedContracts) {
            if (!contractApplied(contract, goal)) {
                result = result.add(contract);
            }
        }
        return result;
    }

    // This seems to be inefficient...
    protected static boolean contractApplied(final LoopContract contract,
                                           final Goal goal) {
        Node selfOrParentNode = goal.node();
        Node previousNode = null;
        while (selfOrParentNode != null) {
            RuleApp app = selfOrParentNode.getAppliedRuleApp();
            if (app instanceof LoopContractInternalBuiltInRuleApp) {
                LoopContractInternalBuiltInRuleApp blockRuleApp =
                        (LoopContractInternalBuiltInRuleApp)app;
                if (blockRuleApp.getBlock().equals(contract.getBlock()) && 
                        selfOrParentNode.getChildNr(previousNode) == 0) {
                    // prevent application of contract in its own check validity branch
                    // but not in other branches, e.g., do-while 
                    // loops might need to apply the same contract 
                    // twice in its usage branch
                    return true;
                }
            }
            previousNode = selfOrParentNode;
            selfOrParentNode = selfOrParentNode.parent();
        }

        Services services = goal.proof().getServices();
        Proof proof = goal.proof();
        ProofOblInput po = services.getSpecificationRepository().getProofOblInput(proof);
        if (po instanceof SymbolicExecutionPO) {
            Goal initiatingGoal = ((SymbolicExecutionPO)po).getInitiatingGoal();
            return contractApplied(contract, initiatingGoal);
        } else {
            return false;
        }
    }

    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence occurrence) {
        if (occursNotAtTopLevelInSuccedent(occurrence)) {
            return false;
        }
        
        // abort if inside of transformer
        if (Transformer.inTransformer(occurrence)) {
            return false;
        }
        
        final Instantiation instantiation =
                instantiate(occurrence.subTerm(), goal, goal.proof().getServices());
        
        if (instantiation == null) {
            return false;
        }
        
        final ImmutableSet<LoopContract> contracts =
                getApplicableContracts(instantiation, goal, goal.proof().getServices());
        
        for (LoopContract contract : contracts) {
        	// The rule is only applicable if the block starts with a while loop.
        	// If the head is not empty, then the block must start with a for loop,
        	// which must be transformed into a while loop before the rule can be applied.
        	if (contract.getHead().isEmpty()) {
        		return true;
        	}
        }
        
        return false;
    }

    public Instantiation instantiate(final Term formula,
                                     final Goal goal,
                                     final Services services) {
        if (formula == getLastFocusTerm()) {
            return getLastInstantiation();
        } else {
            final Instantiation result =
                    new Instantiator(formula, goal, services).instantiate();
            setLastFocusTerm(formula);
            setLastInstantiation(result);
            return result;
        }
    }
    
    protected Map<LocationVariable, Function>
                createAndRegisterAnonymisationVariables(final Iterable<LocationVariable> variables,
                                                        final LoopContract contract,
                                                        final TermServices services) {
        Map<LocationVariable, Function> result = new LinkedHashMap<LocationVariable, Function>(40);
        final TermBuilder tb = services.getTermBuilder();
        for (LocationVariable variable : variables) {
            if(contract.hasModifiesClause(variable)) {
                final String anonymisationName =
                        tb.newName(BlockContractBuilders.ANON_OUT_PREFIX + variable.name());
                final Function anonymisationFunction =
                        new Function(new Name(anonymisationName), variable.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                result.put(variable, anonymisationFunction);
            }
        }
        return result;
    }

    protected static final class Instantiator
            extends AbstractBlockSpecificationElementRule.Instantiator {

        public Instantiator(final Term formula,
                            final Goal goal,
                            final Services services) {
            super(formula, goal, services);
        }

        @Override
        protected boolean hasApplicableContracts(
                                               final Services services,
                                               final StatementBlock block,
                                               final Modality modality,
                                               Goal goal) {
            return !getApplicableContracts(services.getSpecificationRepository(),
                                           block, modality, goal).isEmpty();
        }
    }
}
