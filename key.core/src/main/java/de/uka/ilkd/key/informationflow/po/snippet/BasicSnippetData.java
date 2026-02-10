/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.EnumMap;
import java.util.List;

import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;


/**
 * Immutable class.
 * <p/>
 *
 * @author christoph
 */
class BasicSnippetData {

    /**
     * Tells whether the contract contains a measured_by clause.
     */
    final boolean hasMby;

    /**
     * Variables originally used during parsing.
     */
    final StateVars origVars;

    /**
     * TermBuilder used by the FactoryMethods.
     */
    final TermBuilder tb;

    final Services services;

    /**
     * Unified contract content.
     */
    private final EnumMap<Key, Object> contractContents = new EnumMap<>(Key.class) {

        private static final long serialVersionUID = -8548805965130100236L;

        @Override
        public Object put(Key key, Object value) {
            assert value == null || key.getType().isInstance(value);
            return super.put(key, value);
        }
    };


    /**
     * Keys to access the unified contract content.
     */
    enum Key {

        /**
         * Returns the KeYJavaType representing the class/interface to which the specification
         * element belongs.
         */
        FOR_CLASS(KeYJavaType.class),
        /**
         * Returns the contracted function symbol.
         */
        TARGET_METHOD(IObserverFunction.class),
        /**
         * Returns the contracted block.
         */
        TARGET_BLOCK(StatementBlock.class), PRECONDITION(JTerm.class),
        /**
         * Returns the free precondition.
         */
        FREE_PRECONDITION(JTerm.class), POSTCONDITION(JTerm.class),
        LOOP_INVARIANT(LoopSpecification.class), LOOP_INVARIANT_TERM(JTerm.class),
        MODIFIABLE(JTerm.class), DEPENDENS(JTerm.class), MEASURED_BY(JTerm.class),
        MODALITY(JModality.JavaModalityKind.class), INF_FLOW_SPECS(ImmutableList.class),
        /**
         * Self term of the transformed block contract
         */
        BLOCK_SELF(JTerm.class),
        /**
         * Variables originally used during parsing.
         */
        BLOCK_VARS(AuxiliaryContract.Variables.class), LABELS(Label[].class),
        EXECUTION_CONTEXT(ExecutionContext.class); // this does not fit well here

        private final Class<?> type;


        Key(Class<?> type) {
            this.type = type;
        }


        public Class<?> getType() {
            return type;
        }
    }


    BasicSnippetData(FunctionalOperationContract contract, Services services) {
        this.hasMby = contract.hasMby();
        this.services = services;
        this.tb = services.getTermBuilder();

        contractContents.put(Key.TARGET_METHOD, contract.getTarget());
        contractContents.put(Key.FOR_CLASS, contract.getKJT());
        contractContents.put(Key.PRECONDITION, contract.getPre());
        contractContents.put(Key.POSTCONDITION, contract.getPost());
        contractContents.put(Key.MODIFIABLE, contract.getModifiable());
        contractContents.put(Key.MEASURED_BY, contract.getMby());
        contractContents.put(Key.MODALITY, contract.getModalityKind());

        final JTerm heap = tb.getBaseHeap();
        origVars = new StateVars(contract.getSelf(), contract.getParams(), contract.getResult(),
            contract.getExc(), heap);
    }

    BasicSnippetData(LoopSpecification invariant, ExecutionContext context, JTerm guardTerm,
            Services services) {
        this.hasMby = false;
        this.services = services;
        this.tb = services.getTermBuilder();

        contractContents.put(Key.TARGET_METHOD, invariant.getTarget());
        contractContents.put(Key.FOR_CLASS, invariant.getKJT());
        contractContents.put(Key.EXECUTION_CONTEXT, context);
        contractContents.put(Key.LOOP_INVARIANT, invariant);
        contractContents.put(Key.LOOP_INVARIANT_TERM, invariant.getInvariant(services));
        contractContents.put(Key.MODIFIABLE, invariant.getModifiable());
        contractContents.put(Key.MODALITY, JModality.JavaModalityKind.BOX);
        contractContents.put(Key.INF_FLOW_SPECS, invariant.getInfFlowSpecs(services));

        // add guard term to information flow specs (necessary for soundness)
        // and add the modified specs to the table
        ImmutableList<InfFlowSpec> infFlowSpecs = invariant.getInfFlowSpecs(services);
        ImmutableList<InfFlowSpec> modifiedSpecs = ImmutableSLList.nil();
        for (InfFlowSpec infFlowSpec : infFlowSpecs) {
            ImmutableList<JTerm> modifiedPreExps = infFlowSpec.preExpressions.append(guardTerm);
            ImmutableList<JTerm> modifiedPostExps = infFlowSpec.postExpressions.append(guardTerm);
            InfFlowSpec modifiedSpec =
                new InfFlowSpec(modifiedPreExps, modifiedPostExps, infFlowSpec.newObjects);
            modifiedSpecs = modifiedSpecs.append(modifiedSpec);
        }
        contractContents.put(Key.INF_FLOW_SPECS, modifiedSpecs);

        final JTerm heap = tb.getBaseHeap();
        final ImmutableSet<LocationVariable> localInVariables =
            MiscTools.getLocalIns(invariant.getLoop(), services);
        final ImmutableSet<LocationVariable> localOutVariables =
            MiscTools.getLocalOuts(invariant.getLoop(), services);
        final ImmutableList<JTerm> localInTerms = toTermList(localInVariables);
        final ImmutableList<JTerm> localOutTerms = toTermList(localOutVariables);
        final ImmutableList<JTerm> localInsWithoutOutDuplicates =
            MiscTools.filterOutDuplicates(localInTerms, localOutTerms);
        final ImmutableList<JTerm> localVarsTerms =
            localInsWithoutOutDuplicates.append(localOutTerms);

        origVars = new StateVars(invariant.getInternalSelfTerm(), guardTerm, localVarsTerms, heap);
    }


    BasicSnippetData(InformationFlowContract contract, Services services) {
        this.hasMby = contract.hasMby();
        this.services = services;
        this.tb = services.getTermBuilder();

        contractContents.put(Key.TARGET_METHOD, contract.getTarget());
        contractContents.put(Key.FOR_CLASS, contract.getKJT());
        contractContents.put(Key.PRECONDITION, contract.getPre());
        contractContents.put(Key.FREE_PRECONDITION, contract.getFreePre());
        contractContents.put(Key.MODIFIABLE, contract.getModifiable());
        contractContents.put(Key.DEPENDENS, contract.getDep());
        contractContents.put(Key.MEASURED_BY, contract.getMby());
        contractContents.put(Key.MODALITY, contract.getModalityKind());
        contractContents.put(Key.INF_FLOW_SPECS, contract.getInfFlowSpecs());

        final JTerm heap = tb.getBaseHeap();
        origVars = new StateVars(contract.getSelf(), contract.getParams(), contract.getResult(),
            contract.getExc(), heap);
    }


    BasicSnippetData(BlockContract contract, ExecutionContext context, Services services) {
        this.hasMby = false; // Mby of block contracts is not further considered
        this.services = services;
        this.tb = services.getTermBuilder();

        contractContents.put(Key.TARGET_METHOD, contract.getTarget());
        contractContents.put(Key.FOR_CLASS, contract.getKJT());
        contractContents.put(Key.TARGET_BLOCK, contract.getBlock());
        contractContents.put(Key.BLOCK_VARS, contract.getVariables());
        contractContents.put(Key.BLOCK_SELF, contract.getInstantiationSelfTerm(services));
        contractContents.put(Key.PRECONDITION, contract.getPre(services));
        contractContents.put(Key.POSTCONDITION, contract.getPost(services));
        contractContents.put(Key.MODIFIABLE, contract.getModifiable(services));
        contractContents.put(Key.MODALITY, contract.getModalityKind());
        contractContents.put(Key.INF_FLOW_SPECS, contract.getInfFlowSpecs());
        List<Label> labels = contract.getLabels();
        contractContents.put(Key.LABELS, labels.toArray(new Label[0]));
        contractContents.put(Key.EXECUTION_CONTEXT, context);

        final JTerm heap = tb.getBaseHeap();
        BlockContract.Terms vars = contract.getVariablesAsTerms(services);
        final ImmutableSet<LocationVariable> localInVariables =
            MiscTools.getLocalIns(contract.getBlock(), services);
        final ImmutableSet<LocationVariable> localOutVariables =
            MiscTools.getLocalOuts(contract.getBlock(), services);
        final ImmutableList<JTerm> localInTerms = toTermList(localInVariables);
        final ImmutableList<JTerm> localOutTerms = toTermList(localOutVariables);
        final ImmutableList<JTerm> localInsWithoutOutDuplicates =
            MiscTools.filterOutDuplicates(localInTerms, localOutTerms);
        final ImmutableList<JTerm> localVarsTerms =
            localInsWithoutOutDuplicates.append(localOutTerms);

        origVars = new StateVars(vars.self, localVarsTerms, vars.result, vars.exception, heap);
    }


    private ImmutableList<JTerm> toTermList(ImmutableSet<LocationVariable> vars) {
        ImmutableList<JTerm> result = ImmutableSLList.nil();
        for (ProgramVariable v : vars) {
            result = result.append(tb.var(v));
        }
        return result;
    }


    Object get(Key contentKey) {
        return contractContents.get(contentKey);
    }
}
