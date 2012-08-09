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

    /*public Term getBreak(Label label,
                         Term heapTerm,
                         Term selfTerm,
                         ImmutableList<Term> paramTerms,
                         Map<LocationVariable,Term> atPres,
                         Services services);

    public Term getContinue(Label label,
                         Term heapTerm,
                         Term selfTerm,
                         ImmutableList<Term> paramTerms,
                         Map<LocationVariable,Term> atPres,
                         Services services);

    public Term getReturn(Term heapTerm,
                          Term selfTerm,
                          ImmutableList<Term> paramTerms,
                          Term resultTerm,
                          Map<LocationVariable,Term> atPres,
                          Services services);*/

    public Map<Label, ProgramVariable> getInternalBreakFlags();

    public Map<Label, ProgramVariable> getInternalContinueFlags();

    public ProgramVariable getInternalReturnFlag();

    public void visit(Visitor v);
    
}