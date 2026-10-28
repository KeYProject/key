/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.po;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.infflow.InformationFlowContract;

import org.key_project.logic.Named;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 *
 * @author christoph
 */
@NullMarked
public class InfFlowContractPO extends AbstractInfFlowPO implements ContractPO, InfFlowLeafPO {

    private final InformationFlowContract contract;

    private final ProofObligationVars symbExecVars;

    private final IFProofObligationVars ifVars;

    /**
     * For saving and loading Information-Flow proofs, we need to remember the according taclets,
     * program variables, functions and such.
     */
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();

    public InfFlowContractPO(InitConfig initConfig, InformationFlowContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;

        // generate proof obligation variables
        final IProgramMethod pm = contract.getTarget();
        symbExecVars = new ProofObligationVars(pm, contract.getKJT(), environmentServices);

        assert (symbExecVars.pre.self == null) == (pm.isStatic());
        ifVars = new IFProofObligationVars(symbExecVars, environmentServices);

        // add new information flow symbols
        // (by the way: why only formal parameters?)
        addFormalParamSymbols(infFlowSymbols, symbExecVars.formalParams);
        addFormalParamSymbols(infFlowSymbols, ifVars.c1.formalParams);
        addFormalParamSymbols(infFlowSymbols, ifVars.c2.formalParams);
    }

    /**
     * Registers the formal parameter terms of the given variable assignment
     * with the proof obligation's symbol table. This is a static helper
     * because the constructor may not call instance methods like
     * {@link InfFlowPO#addIFSymbol(JTerm)} on the {@code @UnderInitialization}
     * receiver. The formal parameters are always present at this point (they
     * are built eagerly by {@link ProofObligationVars}), hence the null
     * guard.
     */
    private static void addFormalParamSymbols(InfFlowProofSymbols symbols,
            @Nullable ImmutableList<JTerm> formalParams) {
        if (formalParams == null) {
            throw new NullPointerException(
                "No formal parameter terms for the information flow proof obligation.");
        }
        for (final JTerm formalParam : formalParams) {
            symbols.add(formalParam);
        }
    }

    @Override
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;

        final Services proofServices = postInit();
        final TermBuilder tb = this.tb;
        if (tb == null) {
            throw new NullPointerException("Term builder not initialized.");
        }

        // create proof obligation
        InfFlowPOSnippetFactory f =
            POSnippetFactory.getInfFlowFactory(contract, ifVars.c1, ifVars.c2, proofServices);
        final JTerm selfComposedExec =
            f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION);
        final JTerm post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);
        final JTerm finalTerm = tb.imp(selfComposedExec, post);
        addLabeledIFSymbol(selfComposedExec);

        // register final term, taclets and collect class axioms
        assignPOTerms(finalTerm);
        collectAxioms(contract.getKJT(), proofConfig);

        for (final NoPosTacletApp t : taclets) {
            if (t.taclet().name().toString().startsWith("Class_invariant_axiom")) {
                addIFSymbol(t.taclet());
            }
        }
    }


    /**
     * Collects the class axioms for the given type. The {@code proofConfig}
     * argument is deliberately the {@code proofConfig} field, which is
     * {@code null} in {@code readProblem()} (see the assertion at its
     * start): the information-flow proof obligation performs no proof
     * configuration at this stage and the base axiom registration path
     * tolerates an absent configuration. The base {@code AbstractPO}
     * parameter is not nullness-annotated and cannot be widened from this
     * module.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    private void collectAxioms(KeYJavaType kjt, @Nullable InitConfig proofConfig) {
        collectClassAxioms(kjt, proofConfig);
    }


    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof InfFlowContractPO cPO)) {
            return false;
        }
        return contract.equals(cPO.contract);
    }


    /**
     * {@inheritDoc}
     *
     * Deliberately nullable: {@code null} is returned when the contract has
     * no measured-by clause. {@link ContractPO#getMbyAtPre()} is not
     * nullness-annotated in key.core although all realizations (including
     * {@code DependencyContractPO}) return {@code null} for absent clauses,
     * and none of the callers in key.core dereferences the result (all such
     * call sites are commented out).
     */
    @Override
    @SuppressWarnings("nullness:override.return.invalid")
    public @Nullable JTerm getMbyAtPre() {
        if (contract.hasMby()) {
            return symbExecVars.pre.mbyAtPre;
        } else {
            return null;
        }
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected String buildPOName(boolean transactionFlag) {
        return getContract().getName();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected IProgramMethod getProgramMethod() {
        return contract.getTarget();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isTransactionApplicable() {
        return false;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
        return contract.getKJT();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected JModality.JavaModalityKind getTerminationMarker() {
        return getContract().getModalityKind();
    }


    @Override
    public InformationFlowContract getContract() {
        return contract;
    }


    public IFProofObligationVars getIFVars() {
        return ifVars;
    }

    /**
     * {@inheritDoc}
     *
     * @return
     */
    @Override
    public Configuration createLoaderConfig() {
        var c = super.createLoaderConfig();
        c.set("contract", contract.getName());
        return c;
    }


    @Override
    public InfFlowProofSymbols getIFSymbols() {
        assert infFlowSymbols != null;
        return infFlowSymbols;
    }

    @Override
    public final void addIFSymbol(JTerm t) {
        assert t != null;
        infFlowSymbols.add(t);
    }

    @Override
    public void addIFSymbol(Named n) {
        assert n != null;
        infFlowSymbols.add(n);
    }

    @Override
    public void addLabeledIFSymbol(JTerm t) {
        assert t != null;
        infFlowSymbols.addLabeled(t);
    }

    @Override
    public void addLabeledIFSymbol(Named n) {
        assert n != null;
        infFlowSymbols.addLabeled(n);
    }

    @Override
    public void unionLabeledIFSymbols(InfFlowProofSymbols symbols) {
        assert symbols != null;
        infFlowSymbols = infFlowSymbols.unionLabeled(symbols);
    }

    /**
     * Deliberately returns {@code null}: information flow contracts do not
     * have global defs. {@link AbstractOperationPO} declares a non-null
     * return type although its only caller,
     * {@code createApplyGlobalUpdateTerm}, explicitly null-tolerates the
     * result; the base signature cannot be widened from this module.
     */
    @Override
    @SuppressWarnings("nullness:override.return.invalid")
    protected @Nullable JTerm getGlobalDefs(LocationVariable heap, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Services services) {
        // information flow contracts do not have global defs
        return null;
    }


    @Override
    public IFProofObligationVars getLeafIFVars() {
        return getIFVars();
    }


    // the following code is legacy code
    @Override
    @Deprecated
    protected ImmutableList<StatementBlock> buildOperationBlocks(
            ImmutableList<LocationVariable> formalParVars, ProgramVariable selfVar,
            ProgramVariable resultVar, Services services) {
        throw new UnsupportedOperationException(
            "Not supported any more. " + "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected JTerm getPre(List<LocationVariable> modHeaps, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        throw new UnsupportedOperationException(
            "Not supported any more. " + "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected JTerm getPost(List<LocationVariable> modHeaps, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable exceptionVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        throw new UnsupportedOperationException(
            "Not supported any more. " + "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected JTerm buildFrameClause(List<LocationVariable> modHeaps, Map<JTerm, JTerm> heapToAtPre,
            LocationVariable selfVar, ImmutableList<LocationVariable> paramVars,
            Services services) {
        throw new UnsupportedOperationException(
            "Not supported any more. " + "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected JTerm generateMbyAtPreDef(LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services) {
        throw new UnsupportedOperationException(
            "Not supported any more. " + "Please use the POSnippetFactory instead.");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public KeYJavaType getContainerType() {
        return getContract().getKJT();
    }
}
