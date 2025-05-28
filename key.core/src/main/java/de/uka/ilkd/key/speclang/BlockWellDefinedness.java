/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableSet;

/**
 * A contract for checking the well-definedness of a jml block contract.
 *
 * @author Michael Kirsten
 */
public class BlockWellDefinedness extends StatementWellDefinedness {

    /**
     * The jml block contract.
     */
    private final BlockContract block;

    private BlockWellDefinedness(String name, int id, Type type, IObserverFunction target,
            LocationVariable heap, OriginalVariables origVars, Condition requires, JTerm modifiable,
            JTerm accessible, Condition ensures, JTerm mby, JTerm rep, BlockContract block,
            TermBuilder tb) {
        super(name, id, type, target, heap, origVars, requires, modifiable, accessible, ensures,
            mby, rep, tb);
        this.block = block;
    }

    /**
     * Creates a contract to check well-definedness of a block contract
     *
     * @param block the block belonging to the block contract
     * @param variables the variables of the block contract
     * @param params the parameters of the block
     * @param services the services instance
     */
    public BlockWellDefinedness(BlockContract block, BlockContract.Variables variables,
            ImmutableSet<LocationVariable> params, Services services) {
        super(block.getName(), block.getBlock().getStartPosition().line(), block.getMethod(),
            variables.toOrigVars().add(convertParams(params)), Type.BLOCK_CONTRACT, services);
        assert block != null;
        final LocationVariable h = getHeap();
        this.block = block;
        setRequires(block.getPrecondition(h, variables, services));
        setModifiable(block.hasModifiableClause(h) ? block.getModifiable(h) : TB.strictlyNothing(),
            services);
        setEnsures(block.getPostcondition(h, variables, services));
    }

    @Override
    public BlockWellDefinedness map(UnaryOperator<JTerm> op, Services services) {
        return new BlockWellDefinedness(getName(), id(), type(), getTarget(), getHeap(),
            getOrigVars(), getRequires().map(op), op.apply(getModifiable()),
            op.apply(getAccessible()), getEnsures().map(op), op.apply(getMby()),
            op.apply(getRepresents()), block.map(op, services), services.getTermBuilder());
    }

    @Override
    SequentFormula generateSequent(SequentTerms seq,
            TermServices services) {
        // wd(pre) & (pre & wf(anon) -> wd(modifiable) & {anon^modifiable}(wd(post)))
        final JTerm imp =
            TB.imp(TB.and(seq.pre, seq.wfAnon), TB.and(seq.wdModifiable, seq.anonWdPost));
        final JTerm wdPre = TB.wd(seq.pre);
        return new SequentFormula(TB.apply(seq.context, TB.and(wdPre, imp)));
    }

    @Override
    public BlockContract getStatement() {
        return this.block;
    }

    @Override
    public boolean transactionApplicableContract() {
        return block.isTransactionApplicable();
    }

    @Override
    public Contract setID(int newId) {
        return new BlockWellDefinedness(getName(), newId, type(), getTarget(), getHeap(),
            getOrigVars(), getRequires(), getModifiable(), getAccessible(), getEnsures(), getMby(),
            getRepresents(), getStatement(), TB);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new BlockWellDefinedness(getName(), id(), type(), newPM, getHeap(), getOrigVars(),
            getRequires(), getModifiable(), getAccessible(), getEnsures(), getMby(),
            getRepresents(), getStatement().setTarget(newKJT, newPM), TB);
    }

    @Override
    public String getTypeName() {
        return "Well-Definedness of " + block.getDisplayName();
    }

    @Override
    public VisibilityModifier getVisibility() {
        return block.getVisibility();
    }

    @Override
    public KeYJavaType getKJT() {
        return block.getKJT();
    }

    @Override
    public BlockWellDefinedness combine(WellDefinednessCheck wdc, TermServices services) {
        assert wdc instanceof BlockWellDefinedness;
        final BlockWellDefinedness bwd = (BlockWellDefinedness) wdc;
        assert this.getStatement().getName().equals(bwd.getStatement().getName());
        assert this.getStatement().getBlock().getStartPosition().line() == bwd.getStatement()
                .getBlock().getStartPosition().line();
        assert this.getStatement().getMethod().equals(bwd.getStatement().getMethod());
        assert this.getStatement().getKJT().equals(bwd.getStatement().getKJT());

        super.combine(bwd, services);
        return this;
    }
}
