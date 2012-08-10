package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public interface BlockContract extends FunctionalOperationContract {
    
	public StatementBlock getBlock();

    public Term getPre(LocationVariable heap, Services services);

    public Term getPost(LocationVariable heap, Services services);

    public Term getMod(LocationVariable heap, Services services);

    public Map<Label, ProgramVariable> getInternalBreakFlags();

    public Map<Label, ProgramVariable> getInternalContinueFlags();

    public ProgramVariable getInternalReturnFlag();

    public BlockContract update(StatementBlock newBlock,
                                Map<LocationVariable,Term> newPres,
                                Map<LocationVariable,Term> newPosts,
                                Map<LocationVariable,Term> newMods);

    public void visit(Visitor v);
    
}