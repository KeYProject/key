/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.po;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
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
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.ContractFactory;
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
public class SymbolicExecutionPO extends AbstractInfFlowPO
        implements ContractPO, InfFlowCompositePO {

    private final InformationFlowContract contract;
    private final ProofObligationVars symbExecVars;
    private final Goal initiatingGoal;

    /**
     * For saving and loading Information-Flow proofs, we need to remember the according taclets,
     * program variables, functions and such.
     */
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();

    /**
     * To be used only for auxiliary proofs where the services object of the actual proof has to be
     * used instead of the initial services form the InitConfig.
     */
    public SymbolicExecutionPO(InitConfig initConfig, InformationFlowContract contract,
            ProofObligationVars symbExecVars, Goal initiatingGoal, Services services) {
        this(initConfig, contract, symbExecVars, initiatingGoal);
        this.environmentServices = services;
    }


    public SymbolicExecutionPO(InitConfig initConfig, InformationFlowContract contract,
            ProofObligationVars symbExecVars, Goal initiatingGoal) {
        super(initConfig, buildContractName(contract));
        this.contract = contract;
        this.symbExecVars = symbExecVars;
        this.initiatingGoal = initiatingGoal;
    }

    /**
     * Builds the name of this proof obligation from the contract. The
     * container type of the target method is only available at run time
     * (hence the null guard), so the name cannot be computed inline in the
     * {@code super(...)} call.
     */
    private static String buildContractName(InformationFlowContract contract) {
        final KeYJavaType containerType = contract.getTarget().getContainerType();
        if (containerType == null) {
            throw new NullPointerException(
                "No container type for the target method of the contract.");
        }
        return ContractFactory.generateContractName(contract.getPODisplayName(),
            contract.getKJT(), contract.getTarget(), containerType,
            contract.getTarget().getStartPosition().line());
    }


    @Override
    public void readProblem() throws ProofInputException {
        postInit();
        final TermBuilder tb = this.tb;
        if (tb == null) {
            throw new NullPointerException("Term builder not initialized.");
        }

        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory = POSnippetFactory.getBasicFactory(
            contract, symbExecVars, initiatingGoal.proof().getServices());

        // symbolic execution under precondition
        final JTerm symExec =
            symbExecFactory.create(BasicPOSnippetFactory.Snippet.SYMBOLIC_EXEC_WITH_PRE);

        // register final term
        assignPOTerms(tb.not(symExec));

        // add class axioms
        final Proof initiatingProof = initiatingGoal.proof();
        if (initiatingProof != null) {
            // proof is not loaded
            final ProofOblInput po = specRepos.getProofOblInput(initiatingProof);
            if (po == null) {
                throw new NullPointerException(
                    "No proof obligation input for the initiating proof.");
            }
            final AbstractOperationPO initiatingPO = (AbstractOperationPO) po;
            taclets = initiatingPO.getInitialTaclets();
        }
    }


    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof SymbolicExecutionPO cPO)) {
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


    public Goal getInitiatingGoal() {
        return initiatingGoal;
    }


    /**
     * {@inheritDoc}
     *
     * @return
     */
    @Override
    public Configuration createLoaderConfig() {
        var c = super.createLoaderConfig();
        c.set("Non-interference contract", contract.getName());
        return c;
    }

    @Override
    public InfFlowProofSymbols getIFSymbols() {
        assert infFlowSymbols != null;
        return infFlowSymbols;
    }

    @Override
    public void addIFSymbol(JTerm t) {
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
    public AbstractInfFlowPO getChildPO() {
        Proof initiatingProof = getInitiatingGoal().proof();
        Services initiatingServices = initiatingProof.getServices();
        ProofOblInput initiatingPO =
            initiatingServices.getSpecificationRepository().getProofOblInput(initiatingProof);
        if (initiatingPO instanceof AbstractInfFlowPO infFlowPO) {
            return infFlowPO;
        } else {
            throw new NullPointerException("Information flow auxiliary proof started from "
                + "within a non-information flow proof.");
        }
    }


    @Override
    public IFProofObligationVars getLeafIFVars() {
        return getChildPO().getLeafIFVars();
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
