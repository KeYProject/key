// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.OpReplacer;

public final class BlockContractImpl extends FunctionalOperationContractImpl implements BlockContract {

	private final StatementBlock block;
    private final Map<Label, ProgramVariable> breakFlags;
    private final Map<Label, ProgramVariable> continueFlags;
    private final ProgramVariable returnFlag;

    public BlockContractImpl(String baseName,
	                          String name,
                                  KeYJavaType kjt,	                          
                                  IProgramMethod pm,
            		          Modality modality,
            		          Map<LocationVariable,Term> pres,
            		          Term mby,
            		          Map<LocationVariable,Term> posts,
            		          Map<LocationVariable,Term> mods,
            		          boolean hasRealMod,
            		          ProgramVariable selfVar,
            		          ImmutableList<ProgramVariable> paramVars,
            		          ProgramVariable resultVar,
            		          ProgramVariable excVar,
                                  Map<LocationVariable, LocationVariable> atPreVars,
                                  int id,
                                  boolean toBeSaved,
                                  boolean transaction,
                              StatementBlock block,
                              Map<Label, ProgramVariable> breakFlags, Map<Label, ProgramVariable> continueFlags, ProgramVariable returnFlag) {
	    super(baseName, name, kjt, pm, modality, pres, mby, posts, mods, hasRealMod, selfVar, paramVars, resultVar, excVar, atPreVars, id, toBeSaved, transaction);
        this.block = block;
        this.breakFlags = breakFlags;
        this.continueFlags = continueFlags;
        this.returnFlag = returnFlag;
    }

    @Override
    public StatementBlock getBlock() {
        return block;
    }

    /*public Term getBreak(Label label,
                         ProgramVariable selfVar,
                         ImmutableList<ProgramVariable> paramVars,
                         Map<LocationVariable,? extends ProgramVariable> atPreVars,
                         Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert atPreVars.size() != 0;
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                paramVars,
                null,
                null,
                atPreVars,
                services);
        final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(breaks.get(label));
    }

    public Term getBreak(Label label,
                         Term heapTerm,
                         Term selfTerm,
                         ImmutableList<Term> paramTerms,
                         Map<LocationVariable,Term> atPres,
                         Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert atPres.size() != 0;
        assert services != null;
        final Map<Term, Term> replaceMap = getReplaceMap(heapTerm,
                selfTerm,
                paramTerms,
                null,
                null,
                atPres,
                services);
        final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(breaks.get(label));
    }

    public Term getContinue(Label label,
                         ProgramVariable selfVar,
                         ImmutableList<ProgramVariable> paramVars,
                         Map<LocationVariable,? extends ProgramVariable> atPreVars,
                         Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert atPreVars.size() != 0;
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                paramVars,
                null,
                null,
                atPreVars,
                services);
        final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(continues.get(label));
    }

    public Term getContinue(Label label,
                         Term heapTerm,
                         Term selfTerm,
                         ImmutableList<Term> paramTerms,
                         Map<LocationVariable,Term> atPres,
                         Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert atPres.size() != 0;
        assert services != null;
        final Map<Term, Term> replaceMap = getReplaceMap(heapTerm,
                selfTerm,
                paramTerms,
                null,
                null,
                atPres,
                services);
        final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(continues.get(label));
    }

    public Term getReturn(ProgramVariable selfVar,
                          ImmutableList<ProgramVariable> paramVars,
                          ProgramVariable resultVar,
                          Map<LocationVariable,? extends ProgramVariable> atPreVars,
                          Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert atPreVars.size() != 0;
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                paramVars,
                resultVar,
                null,
                atPreVars,
                services);
        final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(returns);
    }

    public Term getReturn(Term heapTerm,
                         Term selfTerm,
                         ImmutableList<Term> paramTerms,
                         Term resultTerm,
                         Map<LocationVariable,Term> atPres,
                         Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert atPres.size() != 0;
        assert services != null;
        final Map<Term, Term> replaceMap = getReplaceMap(heapTerm,
                selfTerm,
                paramTerms,
                resultTerm,
                null,
                atPres,
                services);
        final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(returns);
    }*/

    public Map<Label, ProgramVariable> getInternalBreakFlags() {
        return breakFlags;
    }

    public Map<Label, ProgramVariable> getInternalContinueFlags() {
        return continueFlags;
    }

    public ProgramVariable getInternalReturnFlag() {
        return returnFlag;
    }

    public ProgramVariable getInternalSelfVar() {
        return originalSelfVar;
    }

    public ImmutableList<ProgramVariable> getInternalParamVars() {
        return originalParamVars;
    }

    public Map<LocationVariable, LocationVariable> getInternalAtPreVars() {
        return originalAtPreVars;
    }

    public ProgramVariable getInternalResultVar() {
        return originalResultVar;
    }

    public ProgramVariable getInternalExcVar() {
        return originalExcVar;
    }

    public BlockContract update(StatementBlock newBlock,
                                Map<LocationVariable,Term> newPres,
                                Map<LocationVariable,Term> newPosts,
                                Map<LocationVariable,Term> newMods) {
        return new BlockContractImpl(baseName, name, kjt, pm, modality, newPres, originalMby, newPosts, newMods, hasRealModifiesClause,
                originalSelfVar, originalParamVars, originalResultVar, originalExcVar, originalAtPreVars, id, toBeSaved,
                transaction, newBlock, breakFlags, continueFlags, returnFlag);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnBlockContract(this);
    }

}