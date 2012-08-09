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

    public Term getPre(LocationVariable heap, Services services) {
        return getPre(heap, originalSelfVar, originalParamVars, originalAtPreVars, services);
    }

    public Term getPost(LocationVariable heap, Services services) {
        return getPost(heap, originalSelfVar, originalParamVars, originalResultVar, originalExcVar, originalAtPreVars, services);
    }

    public Term getMod(LocationVariable heap, Services services) {
        return getMod(heap, originalSelfVar, originalParamVars, services);
    }

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