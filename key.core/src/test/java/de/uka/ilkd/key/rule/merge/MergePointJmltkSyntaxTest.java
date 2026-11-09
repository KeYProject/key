/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.merge;

import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.statement.MergePointStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.rule.merge.procedures.MergeByIfThenElse;
import de.uka.ilkd.key.rule.merge.procedures.MergeTotalWeakening;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.speclang.PredicateAbstractionMergeContract;
import de.uka.ilkd.key.speclang.UnparameterizedMergeContract;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests that the JMLtk 1.2.1 typed {@code JmlMergePointStmt} (the comment form
 * {@code //@ merge_point \by … \lattice … \predicate …;}) is converted to KeY
 * merge contracts with the right procedure, lattice and abstraction predicates.
 * The legacy multi-line {@code merge_proc}/{@code merge_params} form is covered
 * by {@link MergeRuleTests} (it goes through the leftover-comment fallback).
 */
public final class MergePointJmltkSyntaxTest {

    private static final Path NEWSYNTAX =
        HelperClassForTests.TESTCASE_DIRECTORY.resolve("merge/newsyntax");

    /**
     * The merge point statement of the given method of the loaded environment.
     */
    private static MergePointStatement mergePointOf(KeYEnvironment<?> env, String methodName) {
        final Services services = env.getLoadedProof().getServices();
        final JavaInfo javaInfo = services.getJavaInfo();
        final KeYJavaType type = javaInfo.getKeYJavaType("MergeNewSyntax");
        assertThat(type).as("class %s", type).isNotNull();
        for (IProgramMethod pm : javaInfo.getAllProgramMethods(type)) {
            if (!pm.getName().equals(methodName)) {
                continue;
            }
            final JavaASTCollector collector =
                new JavaASTCollector(pm.getBody(), MergePointStatement.class);
            collector.start();
            assertThat(collector.getNodes())
                    .as("merge point statement in %s", methodName)
                    .hasSize(1);
            return (MergePointStatement) collector.getNodes().get(0);
        }
        throw new AssertionError("method " + methodName + " not found");
    }

    /**
     * A bare {@code //@ merge_point;} gets the default {@code MergeByIfThenElse}
     * procedure.
     */
    @Test
    public void bareMergePointGetsDefaultProcedure() throws Exception {
        try (KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(NEWSYNTAX.resolve("merge.newsyntax.bare.key"))) {
            final MergePointStatement mps = mergePointOf(env, "bare");
            assertThat(mps.getMergeContracts()).hasSize(1);
            final MergeContract contract = mps.getMergeContracts().iterator().next();
            assertThat(contract).isInstanceOf(UnparameterizedMergeContract.class);
            assertThat(contract.getMergeProcedure()).isEqualTo(MergeByIfThenElse.class);
        }
    }

    /**
     * The {@code \by} option (plain-identifier form) selects the named procedure.
     */
    @Test
    public void byOptionCarriesProcedureName() throws Exception {
        try (KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(NEWSYNTAX.resolve("merge.newsyntax.byId.key"))) {
            final MergePointStatement mps = mergePointOf(env, "byId");
            assertThat(mps.getMergeContracts()).hasSize(1);
            final MergeContract contract = mps.getMergeContracts().iterator().next();
            assertThat(contract).isInstanceOf(UnparameterizedMergeContract.class);
            assertThat(contract.getMergeProcedure()).isEqualTo(MergeTotalWeakening.class);
        }
    }

    /**
     * The full {@code \by "…" \lattice … \predicate (T v) : …} form yields a
     * predicate-abstraction merge contract with the lattice and the predicates.
     */
    @Test
    public void parametricMergePointCarriesLatticeAndPredicates() throws Exception {
        try (KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(NEWSYNTAX.resolve("merge.newsyntax.param.key"))) {
            final Services services = env.getLoadedProof().getServices();
            final MergePointStatement mps = mergePointOf(env, "param");
            assertThat(mps.getMergeContracts()).hasSize(1);
            final MergeContract contract = mps.getMergeContracts().iterator().next();
            assertThat(contract).isInstanceOf(PredicateAbstractionMergeContract.class);
            final PredicateAbstractionMergeContract pca =
                (PredicateAbstractionMergeContract) contract;
            assertThat(pca.getMergeProcedure())
                    .isEqualTo(MergeWithPredicateAbstraction.class);
            assertThat(pca.getLatticeTypeName()).isEqualTo("conjunctive");
            assertThat(pca.getAbstractionPredicates(pca.getAtPres(), services)).hasSize(2);
        }
    }
}
