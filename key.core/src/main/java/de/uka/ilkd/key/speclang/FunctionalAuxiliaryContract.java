/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.MapUtil;

/**
 * This class is only used to generate a proof obligation for an {@link AuxiliaryContract}.
 *
 * @author lanzinger
 *
 * @param <T> the type of {@link AuxiliaryContract} for which this class generated POs.
 */
public abstract class FunctionalAuxiliaryContract<T extends AuxiliaryContract> implements Contract {


    /**
     * @see #getAuxiliaryContract()
     */
    private T contract;

    /**
     * This contract's ID.
     */
    private final int id;

    /**
     * This contract's name.
     */
    private final String name;

    /**
     * This contract's display name.
     */
    private final String displayName;

    /**
     * This contract's type name.
     */
    private final String typeName;

    /**
     *
     * @param contract a block contract.
     */
    FunctionalAuxiliaryContract(T contract) {
        this(contract, INVALID_ID);
    }

    /**
     *
     * @param contract a block contract.
     * @param id an ID.
     */
    FunctionalAuxiliaryContract(T contract, int id) {
        this.contract = contract;
        this.id = id;

        if (id != INVALID_ID) {
            contract.setFunctionalContract(this);
        }

        name = generateName(contract.getBaseName(),
            str -> ContractFactory.generateContractName(str, getKJT(), getTarget(), getKJT(), id));
        displayName = generateName(contract.getBaseName(),
            str -> ContractFactory.generateDisplayName(str, getKJT(), getTarget(), getKJT(), id));
        typeName = generateName(contract.getBaseName(),
            str -> ContractFactory.generateContractTypeName(str, getKJT(), getTarget(), getKJT()));
    }

    /**
     *
     * @param baseName a base name.
     * @param generator a name generator.
     * @return the generated name.
     */
    private String generateName(String baseName, UnaryOperator<String> generator) {
        return Arrays.stream(baseName.split(SpecificationRepository.CONTRACT_COMBINATION_MARKER))
                .map(generator)
                .reduce(
                    (acc, curr) -> acc + SpecificationRepository.CONTRACT_COMBINATION_MARKER + curr)
                .get();
    }

    @Override
    public boolean isAuxiliary() {
        return true;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public String getDisplayName() {
        return displayName;
    }

    @Override
    public VisibilityModifier getVisibility() {
        throw new UnsupportedOperationException();
    }

    @Override
    public KeYJavaType getKJT() {
        return contract.getKJT();
    }

    @Override
    public int id() {
        return id;
    }

    @Override
    public IProgramMethod getTarget() {
        return contract.getTarget();
    }

    @Override
    public boolean hasMby() {
        return contract.hasMby();
    }

    @Override
    public JTerm getMby() {
        return contract.getMby();
    }

    @Override
    public JTerm getMby(LocationVariable selfVar, ImmutableList<LocationVariable> paramVars,
            Services services) {
        return contract.getMby(selfVar, services);
    }

    @Override
    public JTerm getMby(Map<LocationVariable, JTerm> heapTerms, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres,
            Services services) {
        return contract.getMby(heapTerms, selfTerm, atPres, services);
    }

    @Override
    public OriginalVariables getOrigVars() {
        return contract.getOrigVars();
    }

    @Override
    public JTerm getPre(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        return contract.getPrecondition(heap, selfVar, atPreVars.entrySet().stream().collect(
            MapUtil.collector(
                Map.Entry::getKey, Map.Entry::getValue)),
            services);
    }

    @Override
    public JTerm getPre(List<LocationVariable> heapContext, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        TermBuilder tb = services.getTermBuilder();
        JTerm result = null;

        for (LocationVariable heap : heapContext) {
            final JTerm p = getPre(heap, selfVar, paramVars, atPreVars, services);

            if (result == null) {
                result = p;
            } else {
                result = tb.and(result, p);
            }
        }

        return result;
    }

    @Override
    public JTerm getPre(LocationVariable heap, JTerm heapTerm, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres,
            Services services) {
        return contract.getPrecondition(heap, heapTerm, selfTerm, atPres, services);
    }

    @Override
    public JTerm getPre(List<LocationVariable> heapContext, Map<LocationVariable, JTerm> heapTerms,
            JTerm selfTerm, ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres,
            Services services) {
        TermBuilder tb = services.getTermBuilder();
        JTerm result = null;

        for (LocationVariable heap : heapContext) {
            final JTerm p =
                getPre(heap, heapTerms.get(heap), selfTerm, paramTerms, atPres, services);

            if (result == null) {
                result = p;
            } else if (p != null) {
                result = tb.and(result, p);
            }
        }

        return result;
    }

    @Override
    public JTerm getDep(LocationVariable heap, boolean atPre, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        return services.getTermBuilder().allLocs();
    }

    @Override
    public JTerm getDep(LocationVariable heap, boolean atPre, JTerm heapTerm, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres,
            Services services) {
        return services.getTermBuilder().allLocs();
    }

    @Override
    public JTerm getRequires(LocationVariable heap) {
        return contract.getRequires(heap);
    }

    @Override
    public JTerm getModifiable(LocationVariable heap) {
        return contract.getModifiable(heap);
    }

    @Override
    public JTerm getAccessible(LocationVariable heap) {
        throw new UnsupportedOperationException();
    }

    @Override
    public JTerm getGlobalDefs() {
        throw new UnsupportedOperationException();
    }

    @Override
    public JTerm getGlobalDefs(LocationVariable heap, JTerm heapTerm, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Services services) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getHTMLText(Services services) {
        return contract.getHtmlText(services);
    }

    @Override
    public String getPlainText(Services services) {
        return contract.getPlainText(services);
    }

    @Override
    public boolean toBeSaved() {
        return false;
    }

    @Override
    public boolean transactionApplicableContract() {
        return contract.isTransactionApplicable();
    }

    @Override
    public String proofToString(Services services) {
        return contract.toString();
    }

    @Override
    public ProofOblInput getProofObl(Services services) {
        return services.getSpecificationRepository().getPO(this);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        assert contract instanceof FunctionalBlockContract;
        return new FunctionalBlockContractPO(initConfig, (FunctionalBlockContract) contract);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract,
            boolean supportSymbolicExecutionAPI) {
        return createProofObl(initConfig, contract);
    }

    @Override
    public String getTypeName() {
        return typeName;
    }

    @Override
    public boolean hasSelfVar() {
        return contract.getVariables().self != null;
    }

    /**
     * Returns <code>true</code> iff the method (according to the contract) does not modify the heap
     * at all, i.e., iff it is "strictly pure."
     *
     * @param heap the heap to use.
     * @return <code>true</code> iff this contract is strictly pure.
     * @see AuxiliaryContract#hasModifiableClause(LocationVariable)
     */
    public boolean hasModifiableClause(LocationVariable heap) {
        return contract.hasModifiableClause(heap);
    }

    protected void setAuxiliaryContract(T contract) {
        this.contract = contract;
    }

    /**
     *
     * @return the corresponding {@link AuxiliaryContract}.
     */
    public T getAuxiliaryContract() {
        return contract;
    }

    /**
     *
     * @return the block this contract belongs to.
     * @see AuxiliaryContract#getBlock()
     */
    public StatementBlock getBlock() {
        return contract.getBlock();
    }

    /**
     *
     * @return the method containing {@link #getBlock()}
     * @see AuxiliaryContract#getMethod()
     */
    public IProgramMethod getMethod() {
        return contract.getMethod();
    }

    /**
     * Returns the set of placeholder variables created during this contract's instantiation. These
     * are replaced by the real variables with the same names when the contract is applied.
     *
     * @return the placeholder variables used created during this contracts instantiation.
     * @see AuxiliaryContractBuilders.VariablesCreatorAndRegistrar
     * @see AuxiliaryContract#getPlaceholderVariables()
     */
    public AuxiliaryContract.Variables getPlaceholderVariables() {
        return contract.getPlaceholderVariables();
    }

    /**
     * @return this contract's modality.
     * @see AuxiliaryContract#getModalityKind()
     */
    public JModality.JavaModalityKind getModalityKind() {
        return contract.getModalityKind();
    }
}
