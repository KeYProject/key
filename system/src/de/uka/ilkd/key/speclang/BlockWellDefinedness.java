package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A contract for checking the well-definedness of a jml block contract.
 *
 * @author Michael Kirsten
 */
public class BlockWellDefinedness extends StatementWellDefinedness {

    private final BlockContract block;

    private BlockWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                 LocationVariable heap, OriginalVariables origVars,
                                 Condition requires, Term assignable, Term accessible,
                                 Condition ensures, Term mby, Term rep, BlockContract block) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep);
        this.block = block;
    }

    public BlockWellDefinedness(BlockContract block, ImmutableSet<ProgramVariable> params,
                                Services services) {
        super(block.getName(), block.getBlock().getStartPosition().getLine(), block.getMethod(),
              block.getOrigVars().add(convertParams(params)), Type.BLOCK_CONTRACT, services);
        assert block != null;
        final LocationVariable h = getHeap();
        this.block = block;
        setRequires(block.getRequires(h));
        setAssignable(block.getAssignable(h), services);
        setEnsures(block.getEnsures(h));
    }

    SequentFormula generateSequent(SequentTerms seq, Services services) {
        // wd(pre) & (pre & wf(anon) -> wd(mod) & {anon^mod}(wd(ppost)))
        final Term imp = TB.imp(TB.and(seq.pre, seq.wfAnon),
                                TB.and(seq.wdMod, seq.anonWdPost));
        final Term wdPre = TB.wd(seq.pre, services);
        return new SequentFormula(TB.apply(seq.context,
                                           TB.and(wdPre, imp)));
    }

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
                                        getOrigVars(), getRequires(), getAssignable(),
                                        getAccessible(), getEnsures(), getMby(),
                                        getRepresents(), getStatement());
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new BlockWellDefinedness(getName(), id(), type(), newPM, getHeap(),
                                        getOrigVars(), getRequires(), getAssignable(),
                                        getAccessible(), getEnsures(), getMby(),
                                        getRepresents(), getStatement().setTarget(newKJT, newPM));
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
}