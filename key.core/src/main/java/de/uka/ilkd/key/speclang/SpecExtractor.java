/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Extracts specifications from comments.
 */
public interface SpecExtractor {

    /**
     * Returns the operation contracts for the passed operation.
     */
    ImmutableSet<SpecificationElement> extractMethodSpecs(IProgramMethod pm)
            throws SLTranslationException;

    ImmutableSet<SpecificationElement> extractMethodSpecs(IProgramMethod pm,
            boolean addInvariant) throws SLTranslationException;

    /**
     * Returns the class invariants for the passed type.
     */
    ImmutableSet<SpecificationElement> extractClassSpecs(KeYJavaType kjt)
            throws SLTranslationException;

    /**
     * Returns the loop invariant for the passed loop (if any).
     */
    LoopSpecification extractLoopInvariant(IProgramMethod pm, LoopStatement loop)
            throws SLTranslationException;

    /**
     * Returns the block contracts for the passed block.
     *
     * @param method the program method
     * @param block the statement block
     * @return the block contracts
     */
    ImmutableSet<BlockContract> extractBlockContracts(IProgramMethod method,
            StatementBlock block) throws SLTranslationException;

    /**
     * Returns the loop contracts for the passed block.
     *
     * @param method the program method containing the block.
     * @param block the block.
     * @return the loop contracts
     * @throws SLTranslationException a translation exception
     */
    ImmutableSet<LoopContract> extractLoopContracts(IProgramMethod method,
            StatementBlock block) throws SLTranslationException;

    /**
     * Returns the loop contracts for the passed loop.
     *
     * @param method the program method containing the loop.
     * @param loop the loop.
     * @return the loop contracts
     * @throws SLTranslationException a translation exception
     */
    ImmutableSet<LoopContract> extractLoopContracts(IProgramMethod method,
            LoopStatement loop) throws SLTranslationException;

    /**
     * Returns the {@link MergeContract}s for the given {@link MergePointStatement}.
     *
     * @param methodParams TODO
     */
    ImmutableSet<MergeContract> extractMergeContracts(IProgramMethod method,
            MergePointStatement mps, ImmutableList<ProgramVariable> methodParams)
            throws SLTranslationException;

    /**
     * Returns the block contracts for the passed labeled statement if it labels a block.
     *
     * @param method the program method
     * @param labeled the labeled statement
     * @return the block contracts
     * @throws SLTranslationException a translation exception
     */
    ImmutableSet<BlockContract> extractBlockContracts(IProgramMethod method,
            LabeledStatement labeled) throws SLTranslationException;

    /**
     * Returns the loop contracts for the passed labeled statement if it labels a block.
     *
     * @param method the program method
     * @param labeled the labeled statement
     * @return the loop contracts
     * @throws SLTranslationException a translation exception
     */
    ImmutableSet<LoopContract> extractLoopContracts(IProgramMethod method,
            LabeledStatement labeled) throws SLTranslationException;

    /**
     * Returns all warnings generated so far in the translation process. (e.g. this may warn about
     * unsupported features which have been ignored by the translation)
     */
    ImmutableList<PositionedString> getWarnings();
}
