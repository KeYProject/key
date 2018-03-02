package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.util.InfFlowSpec;

public final class SimpleLoopContract
        extends AbstractBlockSpecificationElement implements LoopContract {
	
    private final Term decreases;

    public static LoopContract combine(ImmutableSet<LoopContract> contracts, Services services) {
        return new Combinator(
                contracts.toArray(new LoopContract[contracts.size()]),
                services)
                .combine();
    }
    
    private ImmutableSet<FunctionalLoopContract> functionalContracts;

    public SimpleLoopContract(final String baseName,
                               final StatementBlock block,
                               final List<Label> labels,
                               final IProgramMethod method,
                               final Modality modality,
                               final Map<LocationVariable, Term> preconditions,
                               final Term measuredBy,
                               final Map<LocationVariable, Term> postconditions,
                               final Map<LocationVariable, Term> modifiesClauses,
                               final ImmutableList<InfFlowSpec> infFlowSpecs,
                               final Variables variables,
                               final boolean transactionApplicable,
                               final Map<LocationVariable,Boolean> hasMod,
                               final Term decreases,
                               ImmutableSet<FunctionalLoopContract> functionalContracts) {
        super(baseName,
                block,
                labels,
                method,
                modality,
                preconditions,
                measuredBy,
                postconditions,
                modifiesClauses,
                infFlowSpecs,
                variables,
                transactionApplicable,
                hasMod);
        
        this.decreases = decreases;
        this.functionalContracts = functionalContracts;
    }
    
    @Override
    public Term getDecreases() {
    	return decreases;
    }
    
    @Override
    public ImmutableSet<FunctionalLoopContract> getFunctionalContracts() {
        return functionalContracts;
    }

    @Override
    public void setFunctionalLoopContract(FunctionalLoopContract contract) {
        assert contract.id() != Contract.INVALID_ID;
        assert contract.getLoopContract().equals(this);
        
        functionalContracts = DefaultImmutableSet.<FunctionalLoopContract>nil().add(contract);
    }

    @Override
    public void visit(final Visitor visitor) {
        assert visitor != null;
        visitor.performActionOnLoopContract(this);
    }

    @Override
    public String getName() {
        return "Loop Contract";
    }

    @Override
    public String getUniqueName() {
        if (getTarget() != null)
            return "Loop Contract " + getBlock().getStartPosition().getLine() +
                    " " + getTarget().getUniqueName();
        else
            return "Loop Contract " + getBlock().getStartPosition().getLine() +
                    " " + Math.abs(getBlock().hashCode());
    }

    @Override
    public String getDisplayName() {
        return "Loop Contract";
    }

    @Override
    public LoopContract update(final StatementBlock newBlock,
                                final Map<LocationVariable,Term> newPreconditions,
                                final Map<LocationVariable,Term> newPostconditions,
                                final Map<LocationVariable,Term> newModifiesClauses,
                                final ImmutableList<InfFlowSpec> newinfFlowSpecs,
                                final Variables newVariables) {
        return new SimpleLoopContract(baseName, newBlock, labels, method, modality,
                                       newPreconditions, measuredBy, newPostconditions,
                                       newModifiesClauses, newinfFlowSpecs,
                                       newVariables,
                                       transactionApplicable, hasMod, decreases,
                                       functionalContracts);
    }

    @Override 
    public LoopContract setBlock(StatementBlock newBlock) {
        return update(newBlock, preconditions, postconditions, modifiesClauses,
                      infFlowSpecs, variables);
    }

    public LoopContract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        assert newKJT.equals(newPM.getContainerType());
        return new SimpleLoopContract(baseName, block, labels, (IProgramMethod)newPM, modality,
                                       preconditions, measuredBy, postconditions, modifiesClauses,
                                       infFlowSpecs, variables, transactionApplicable, hasMod,
                                       decreases, functionalContracts);
    }

    @Override
    public String toString() {
        return "SimpleLoopContract [block=" + block + ", labels=" + labels
                + ", method=" + method + ", modality=" + modality
                + ", instantiationSelf=" + instantiationSelf
                + ", preconditions=" + preconditions + ", postconditions="
                + postconditions + ", modifiesClauses=" + modifiesClauses
                + ", infFlowSpecs=" + infFlowSpecs
                + ", variables=" + variables
                + ", transactionApplicable=" + transactionApplicable
                + ", hasMod=" + hasMod + "]";
    }
    
    public static class Creator
            extends AbstractBlockSpecificationElement.Creator<LoopContract> {
    	
    	private Term decreases;

        public Creator(String baseName, StatementBlock block,
                List<Label> labels, IProgramMethod method, Behavior behavior,
                Variables variables, Map<LocationVariable, Term> requires,
                Term measuredBy, Map<LocationVariable, Term> ensures,
                ImmutableList<InfFlowSpec> infFlowSpecs,
                Map<Label, Term> breaks, Map<Label, Term> continues,
                Term returns, Term signals, Term signalsOnly, Term diverges,
                Map<LocationVariable, Term> assignables,
                Map<LocationVariable, Boolean> hasMod, Term decreases, Services services) {
            super(baseName, block, labels, method, behavior, variables, requires,
                    measuredBy, ensures, infFlowSpecs, breaks, continues, returns, signals,
                    signalsOnly, diverges, assignables, hasMod, services);
            
            this.decreases = decreases;

            //TODO For now, only blocks that begin with a while loop may have a loop contract.
            // This should later be expanded to include blocks that begin with for and do-while loops,
            // as well as free-standing loops that are not inside of a block.
            if (!(block.getFirstElement() instanceof While)) {
                throw new IllegalArgumentException(
                        "Only blocks that begin with a while loop may have a loop contract! \n"
                		+ "This block begins with " + block.getFirstElement());
            }
        }

        @Override
        protected LoopContract build(String baseName,
                StatementBlock block, List<Label> labels, IProgramMethod method,
                Modality modality, Map<LocationVariable, Term> preconditions,
                Term measuredBy, Map<LocationVariable, Term> postconditions,
                Map<LocationVariable, Term> modifiesClauses,
                ImmutableList<InfFlowSpec> infFlowSpecs, Variables variables,
                boolean transactionApplicable,
                Map<LocationVariable, Boolean> hasMod) {
        	return new SimpleLoopContract(
            		baseName, block, labels, method, modality, preconditions,
                    measuredBy, postconditions, modifiesClauses, infFlowSpecs, variables,
                    transactionApplicable, hasMod, decreases, null);
        }
    }
    
    protected static class Combinator
            extends AbstractBlockSpecificationElement.Combinator<LoopContract> {

        public Combinator(LoopContract[] contracts, Services services) {
            super(contracts, services);
        }

        @Override
        protected LoopContract combine() {
            assert contracts.length > 0;
            if (contracts.length == 1) {
                return contracts[0];
            }
            
            final LoopContract head = contracts[0];
            String baseName = head.getBaseName();
            
            for (int i = 1; i < contracts.length; i++) {
                assert contracts[i].getBlock().equals(head.getBlock());
                
                baseName += SpecificationRepository.CONTRACT_COMBINATION_MARKER
                        + contracts[i].getBaseName();
            }
            
            placeholderVariables = head.getPlaceholderVariables();
            remembranceVariables = placeholderVariables.combineRemembranceVariables();
            
            ImmutableSet<FunctionalLoopContract> functionalContracts = 
                    DefaultImmutableSet.nil();
            
            for (LoopContract contract : contracts) {
                addConditionsFrom(contract);
                functionalContracts = functionalContracts.union(contract.getFunctionalContracts());
            }
            
            Map<LocationVariable,Boolean> hasMod = new LinkedHashMap<LocationVariable, Boolean>();
            for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                boolean hm = false;
                
                for (int i = 1; i < contracts.length && !hm; i++) {
                    hm = contracts[i].hasModifiesClause(heap);
                }
                hasMod.put(heap, hm);
            }
            
            SimpleLoopContract result = new SimpleLoopContract(baseName, 
                                           head.getBlock(), head.getLabels(),
                                           head.getMethod(), head.getModality(), preconditions,
                                           contracts[0].getMby(),
                                           postconditions, modifiesClauses, head.getInfFlowSpecs(),
                                           placeholderVariables,
                                           head.isTransactionApplicable(), hasMod, contracts[0].getDecreases(),
                                           functionalContracts);
            
            return result;
        }
    }
}
