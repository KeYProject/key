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
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.ContractFactory;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.logic.Named;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class LoopInvExecutionPO extends AbstractInfFlowPO implements InfFlowCompositePO {

    private final LoopSpecification loopInvariant;

    private final ProofObligationVars symbExecVars;

    private final JTerm guardTerm;

    private final Goal initiatingGoal;

    private final ExecutionContext context;

    /**
     * For saving and loading Information-Flow proofs, we need to remember the according taclets,
     * program variables, functions and such.
     */
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();

    /**
     * To be used only for auxiliary proofs where the services object of the actual proof has to be
     * used instead of the initial services form the InitConfig.
     */
    public LoopInvExecutionPO(InitConfig initConfig, LoopSpecification loopInv,
            ProofObligationVars symbExecVars, Goal initiatingGoal, ExecutionContext context,
            JTerm guardTerm, Services services) {
        this(initConfig, loopInv, symbExecVars, initiatingGoal, context, guardTerm);
        this.environmentServices = services;
    }


    public LoopInvExecutionPO(InitConfig initConfig, LoopSpecification loopInv,
            ProofObligationVars symbExecVars, Goal initiatingGoal, ExecutionContext context,
            JTerm guardTerm) {
        super(initConfig, buildContractName(loopInv));
        this.loopInvariant = loopInv;
        this.symbExecVars = symbExecVars;
        this.initiatingGoal = initiatingGoal;
        this.context = context;
        this.guardTerm = guardTerm;

        // consistency check
        assert preAndPostExpressionsEqual(loopInv, environmentServices)
                : "Information flow loop invariant malformed. Pre expressions"
                    + "do not match post expressions.";
    }

    /**
     * Builds the name of this proof obligation from the loop invariant. The
     * container type of the target method is only available at run time
     * (hence the null guard), so the name cannot be computed inline in the
     * {@code super(...)} call.
     */
    private static String buildContractName(LoopSpecification loopInv) {
        final IProgramMethod target = loopInv.getTarget();
        if (target == null) {
            throw new NullPointerException(
                "No target method for the loop invariant of the proof obligation.");
        }
        final KeYJavaType containerType = target.getContainerType();
        if (containerType == null) {
            throw new NullPointerException(
                "No container type for the target method of the loop invariant.");
        }
        return ContractFactory.generateContractName(loopInv.getName(), loopInv.getKJT(),
            target, containerType, loopInv.getLoop().getStartPosition().line());
    }

    /**
     * Checks that the pre and post expressions of all information flow
     * specifications of the loop invariant coincide. Static because it is
     * invoked from the constructor, where instance methods may not be called
     * on the {@code @UnderInitialization} receiver.
     */
    private static boolean preAndPostExpressionsEqual(LoopSpecification loopInvariant,
            Services services) {
        for (InfFlowSpec infFlowSpec : loopInvariant.getInfFlowSpecs(services)) {
            if (infFlowSpec.preExpressions == infFlowSpec.postExpressions) {
                return false;
            }
        }
        return true;
    }


    @Override
    public void readProblem() throws ProofInputException {
        postInit();
        final TermBuilder tb = this.tb;
        if (tb == null) {
            throw new NullPointerException("Term builder not initialized.");
        }

        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory = POSnippetFactory.getBasicFactory(loopInvariant,
            symbExecVars, context, guardTerm, environmentServices);

        // symbolic execution
        JTerm symExec = symbExecFactory.create(BasicPOSnippetFactory.Snippet.LOOP_EXEC_WITH_INV);

        // final symbolic execution term
        JTerm finalTerm = tb.applyElementary(symbExecVars.pre.heap, tb.not(symExec));

        // register final term
        assignPOTerms(finalTerm);

        // add class axioms
        Proof initiatingProof = initiatingGoal.proof();
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
        if (!(po instanceof LoopInvExecutionPO lPO)) {
            return false;
        }
        return loopInvariant.equals(lPO.loopInvariant);
    }

    public LoopSpecification getLoopInvariant() {
        return loopInvariant;
    }

    public Goal getInitiatingGoal() {
        return initiatingGoal;
    }

    public ExecutionContext getExecutionContext() {
        return context;
    }

    public JTerm getGuard() {
        return guardTerm;
    }

    @Override
    protected IProgramMethod getProgramMethod() {
        final IProgramMethod target = loopInvariant.getTarget();
        if (target == null) {
            throw new NullPointerException(
                "No target method for the loop invariant of the proof obligation.");
        }
        return target;
    }

    @Override
    protected boolean isTransactionApplicable() {
        return false;
    }

    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
        assert false;
        return loopInvariant.getKJT();
    }

    @Override
    protected JModality.JavaModalityKind getTerminationMarker() {
        return JModality.JavaModalityKind.BOX;
    }

    @Override
    protected String buildPOName(boolean transactionFlag) {
        return loopInvariant.getName();
    }

    /**
     * {@inheritDoc}
     *
     * @return
     */
    @Override
    public Configuration createLoaderConfig() {
        var c = super.createLoaderConfig();
        c.set("Non-interference contract", loopInvariant.getUniqueName());
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
    protected JTerm generateMbyAtPreDef(LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services) {
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
}
