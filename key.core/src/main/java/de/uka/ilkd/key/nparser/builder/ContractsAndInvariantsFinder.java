/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser.builder;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.nparser.JavaKeYParser;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.dl.translation.DLSpecFactory;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.QuantifiableVariable;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This visitor finds all contracts and invariant clauses in {@link KeyAst}.
 *
 * @author Alexander Weigl
 * @version 1 (12/4/19)
 */
@NullMarked
public class ContractsAndInvariantsFinder extends ExpressionBuilder {
    private final DeclarationBuilder declarationBuilder;
    private final List<Contract> contracts = new ArrayList<>();
    private final List<ClassInvariant> invariants = new ArrayList<>();


    private LocationVariable selfVar;

    /**
     * The {@code self} variable is discovered while the AST is visited, after construction; the
     * difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:initialization.fields.uninitialized")
    public ContractsAndInvariantsFinder(Services services, NamespaceSet nss) {
        super(services, nss);
        declarationBuilder = new DeclarationBuilder(services, nss);
    }

    public @NonNull List<Contract> getContracts() {
        return contracts;
    }

    public @NonNull List<ClassInvariant> getInvariants() {
        return invariants;
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitDecls(JavaKeYParser.DeclsContext ctx) {
        mapOf(ctx.contracts());
        mapOf(ctx.invariants());
        return null;
    }

    @Override
    public Object visitContracts(JavaKeYParser.ContractsContext ctx) {
        return mapOf(ctx.one_contract());
    }

    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitOne_contract(JavaKeYParser.One_contractContext ctx) {
        String contractName = visitSimple_ident(ctx.contractName);
        // for program variable declarations
        Namespace<IProgramVariable> oldProgVars = namespaces().programVariables();
        namespaces().setProgramVariables(new Namespace<>(oldProgVars));
        declarationBuilder.visitProg_var_decls(ctx.prog_var_decls());
        JTerm fma = Objects.requireNonNull(accept(ctx.fma));
        JTerm modifiableClause = Objects.requireNonNull(accept(ctx.modifiableClause));
        DLSpecFactory dsf = new DLSpecFactory(getServices());
        try {
            FunctionalOperationContract dlOperationContract =
                dsf.createDLOperationContract(contractName, fma, modifiableClause);
            contracts.add(dlOperationContract);
        } catch (ProofInputException e) {
            semanticError(ctx, Objects.requireNonNull(e.getMessage()));
        }
        // dump local program variable declarations
        namespaces().setProgramVariables(oldProgVars);
        return null;
    }


    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitInvariants(JavaKeYParser.InvariantsContext ctx) {
        Namespace<QuantifiableVariable> orig = variables();
        selfVar = (LocationVariable) ctx.selfVar.accept(this);
        ctx.one_invariant().forEach(it -> it.accept(this));
        unbindVars(orig);
        return null;
    }

    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitOne_invariant(JavaKeYParser.One_invariantContext ctx) {
        String invName = visitSimple_ident(ctx.simple_ident());
        JTerm fma = Objects.requireNonNull(accept(ctx.fma));
        String displayName = ctx.displayName != null ? ctx.displayName.getText() : null;
        DLSpecFactory dsf = new DLSpecFactory(getServices());
        try {
            ClassInvariant inv = dsf.createDLClassInvariant(invName, displayName, selfVar, fma);
            invariants.add(inv);
        } catch (ProofInputException e) {
            semanticError(ctx, Objects.requireNonNull(e.getMessage()));
        }
        return null;
    }

}
