// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.MergeIfThenElse;

/**
 * A {@link MergeContract} for unparameterized {@link MergeProcedure}s like
 * {@link MergeIfThenElse}.
 *
 * @author Dominic Scheurer
 */
public class UnparameterizedMergeContract implements MergeContract {

    private final static String NAME = "Unparametrized Merge Contract";

    private final Class<? extends MergeProcedure> mergeProcedure;
    private final MergePointStatement mps;
    private final KeYJavaType kjt;

    public UnparameterizedMergeContract(
            Class<? extends MergeProcedure> mergeProcedure,
            MergePointStatement mps, KeYJavaType kjt) {
        this.mergeProcedure = mergeProcedure;
        this.mps = mps;
        this.kjt = kjt;
    }

    @Override
    public Class<? extends MergeProcedure> getMergeProcedure() {
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
