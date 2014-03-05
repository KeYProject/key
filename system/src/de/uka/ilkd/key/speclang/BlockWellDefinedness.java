// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
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
                                 Condition ensures, Term mby, Term rep, BlockContract block,
                                 TermBuilder tb) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep, tb);
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
        setAssignable(block.hasModifiesClause(h) ? block.getAssignable(h) : TB.strictlyNothing(),
                      services);
        setEnsures(block.getEnsures(h));
    }

    @Override
    SequentFormula generateSequent(SequentTerms seq, TermServices services) {
        // wd(pre) & (pre & wf(anon) -> wd(mod) & {anon^mod}(wd(post)))
        final Term imp = TB.imp(TB.and(seq.pre, seq.wfAnon),
                                TB.and(seq.wdMod, seq.anonWdPost));
        final Term wdPre = TB.wd(seq.pre);
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
                                        getRepresents(), getStatement(), TB);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new BlockWellDefinedness(getName(), id(), type(), newPM, getHeap(),
                                        getOrigVars(), getRequires(), getAssignable(),
                                        getAccessible(), getEnsures(), getMby(),
                                        getRepresents(),
                                        getStatement().setTarget(newKJT, newPM), TB);
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
        final BlockWellDefinedness bwd = (BlockWellDefinedness)wdc;
        assert this.getStatement().getName().equals(bwd.getStatement().getName());
        assert this.getStatement().getBlock().getStartPosition().getLine() ==
                bwd.getStatement().getBlock().getStartPosition().getLine();
        assert this.getStatement().getMethod().equals(bwd.getStatement().getMethod());
        assert this.getStatement().getKJT().equals(bwd.getStatement().getKJT());

        super.combine(bwd, services);
        return this;
    }
}