// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.util.InfFlowSpec;

/**
 * Default implementation of {@link BlockContract}.
 * 
 * @see SimpleBlockContract.Creator
 */
public final class SimpleBlockContract
        extends AbstractBlockSpecificationElement implements BlockContract {

    public static BlockContract combine(ImmutableSet<BlockContract> contracts, Services services) {
        return new Combinator(
                contracts.toArray(new BlockContract[contracts.size()]),
                services)
                .combine();
    }
	
	private ImmutableSet<FunctionalBlockContract> functionalContracts;

    public SimpleBlockContract(final String baseName,
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
                               ImmutableSet<FunctionalBlockContract> functionalContracts) {
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
        
        this.functionalContracts = functionalContracts;
    }
    
    @Override
	public ImmutableSet<FunctionalBlockContract> getFunctionalContracts() {
    	return functionalContracts;
    }

    @Override
	public void setFunctionalBlockContract(FunctionalBlockContract contract) {
    	assert contract.id() != Contract.INVALID_ID;
    	assert contract.getBlockContract().equals(this);
    	
    	functionalContracts = DefaultImmutableSet.<FunctionalBlockContract>nil().add(contract);
    }

    @Override
    public void visit(final Visitor visitor) {
        assert visitor != null;
        visitor.performActionOnBlockContract(this);
    }

    @Override
    public String getName() {
        return "Block Contract";
    }

    @Override
    public String getUniqueName() {
        if (getTarget() != null)
            return "Block Contract " + getBlock().getStartPosition().getLine() +
                    " " + getTarget().getUniqueName();
        else
            return "Block Contract " + getBlock().getStartPosition().getLine() +
                    " " + Math.abs(getBlock().hashCode());
    }

    @Override
    public String getDisplayName() {
        return "Block Contract";
    }

    @Override
    public BlockContract update(final StatementBlock newBlock,
                                final Map<LocationVariable,Term> newPreconditions,
                                final Map<LocationVariable,Term> newPostconditions,
                                final Map<LocationVariable,Term> newModifiesClauses,
                                final ImmutableList<InfFlowSpec> newinfFlowSpecs,
                                final Variables newVariables,
                                Term newMeasuredBy) {
        return new SimpleBlockContract(baseName, newBlock, labels, method, modality,
                                       newPreconditions, newMeasuredBy, newPostconditions,
                                       newModifiesClauses, newinfFlowSpecs,
                                       newVariables,
                                       transactionApplicable, hasMod, functionalContracts);
    }

    @Override 
    public BlockContract setBlock(StatementBlock newBlock) {
        return update(newBlock, preconditions, postconditions, modifiesClauses,
                      infFlowSpecs, variables, measuredBy);
    }

    public BlockContract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        assert newKJT.equals(newPM.getContainerType());
        return new SimpleBlockContract(baseName, block, labels, (IProgramMethod)newPM, modality,
                                       preconditions, measuredBy, postconditions, modifiesClauses,
                                       infFlowSpecs, variables, transactionApplicable, hasMod,
                                       functionalContracts);
    }

    @Override
    public String toString() {
        return "SimpleBlockContract [block=" + block + ", labels=" + labels
                + ", method=" + method + ", modality=" + modality
                + ", instantiationSelf=" + instantiationSelf
                + ", preconditions=" + preconditions + ", postconditions="
                + postconditions + ", modifiesClauses=" + modifiesClauses
                + ", infFlowSpecs=" + infFlowSpecs
                + ", variables=" + variables
                + ", transactionApplicable=" + transactionApplicable
                + ", hasMod=" + hasMod + "]";
    }
    
    /**
     * This class is used to build {@link SimpleBlockContract}s.
     * 
     * @see Creator#create()
     */
    public static class Creator
            extends AbstractBlockSpecificationElement.Creator<BlockContract> {

        public Creator(String baseName, StatementBlock block,
                List<Label> labels, IProgramMethod method, Behavior behavior,
                Variables variables, Map<LocationVariable, Term> requires,
                Term measuredBy, Map<LocationVariable, Term> ensures,
                ImmutableList<InfFlowSpec> infFlowSpecs,
                Map<Label, Term> breaks, Map<Label, Term> continues,
                Term returns, Term signals, Term signalsOnly, Term diverges,
                Map<LocationVariable, Term> assignables,
                Map<LocationVariable, Boolean> hasMod, Services services) {
            super(baseName, block, labels, method, behavior, variables, requires,
                    measuredBy, ensures, infFlowSpecs, breaks, continues, returns, signals,
                    signalsOnly, diverges, assignables, hasMod, services);
        }

        @Override
        protected BlockContract build(String baseName,
                StatementBlock block, List<Label> labels, IProgramMethod method,
                Modality modality, Map<LocationVariable, Term> preconditions,
                Term measuredBy, Map<LocationVariable, Term> postconditions,
                Map<LocationVariable, Term> modifiesClauses,
                ImmutableList<InfFlowSpec> infFlowSpecs, Variables variables,
                boolean transactionApplicable,
                Map<LocationVariable, Boolean> hasMod) {
            return new SimpleBlockContract(baseName, block, labels, method, modality, preconditions,
                    measuredBy, postconditions, modifiesClauses, infFlowSpecs, variables,
                    transactionApplicable, hasMod, null);
        }
    }
    
    protected static class Combinator
            extends AbstractBlockSpecificationElement.Combinator<BlockContract> {

        public Combinator(BlockContract[] contracts, Services services) {
            super(contracts, services);
        }

        @Override
        protected BlockContract combine() {
            assert contracts.length > 0;
            if (contracts.length == 1) {
                return contracts[0];
            }
            
            final BlockContract head = contracts[0];
            String baseName = head.getBaseName();
            
            for (int i = 1; i < contracts.length; i++) {
                assert contracts[i].getBlock().equals(head.getBlock());
                
                baseName += SpecificationRepository.CONTRACT_COMBINATION_MARKER
                        + contracts[i].getBaseName();
            }
            
            placeholderVariables = head.getPlaceholderVariables();
            remembranceVariables = placeholderVariables.combineRemembranceVariables();
            
            ImmutableSet<FunctionalBlockContract> functionalContracts = 
                    DefaultImmutableSet.nil();
            
            for (BlockContract contract : contracts) {
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
            
            SimpleBlockContract result = new SimpleBlockContract(baseName, 
                                           head.getBlock(), head.getLabels(),
                                           head.getMethod(), head.getModality(), preconditions,
                                           contracts[0].getMby(),
                                           postconditions, modifiesClauses, head.getInfFlowSpecs(),
                                           placeholderVariables,
                                           head.isTransactionApplicable(), hasMod,
                                           functionalContracts);
            
            return result;
        }
    }
}