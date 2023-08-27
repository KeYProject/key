/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.MergeByIfThenElse;
import de.uka.ilkd.key.rule.merge.procedures.UnparametricMergeProcedure;

/**
 * A {@link MergeContract} for {@link UnparametricMergeProcedure}s like {@link MergeByIfThenElse}.
 *
 * @author Dominic Scheurer
 */
public class UnparameterizedMergeContract implements MergeContract {

    private final static String NAME = "Unparametrized Merge Contract";

    private final MergeProcedure mergeProcedure;
    private final MergePointStatement mps;
    private final KeYJavaType kjt;

    public UnparameterizedMergeContract(MergeProcedure mergeProcedure, MergePointStatement mps,
            KeYJavaType kjt) {
        this.mergeProcedure = mergeProcedure;
        this.mps = mps;
        this.kjt = kjt;
    }

    @Override
    public UnparameterizedMergeContract map(UnaryOperator<Term> op, Services services) {
        return this;
    }

    @Override
    public Class<? extends MergeProcedure> getMergeProcedure() {
        return mergeProcedure.getClass();
    }

    @Override
    public MergeProcedure getInstantiatedMergeProcedure(Services services) {
        return mergeProcedure;
    }

    @Override
    public MergePointStatement getMergePointStatement() {
        return mps;
    }

    @Override
    public String getName() {
        return NAME;
    }

    @Override
    public String getDisplayName() {
        return NAME;
    }

    @Override
    public KeYJavaType getKJT() {
        return kjt;
    }

}
