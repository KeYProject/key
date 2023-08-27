/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.ArrayList;
import java.util.List;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.dl.translation.DLSpecFactory;

/**
 * This visitor finds all contracts and invariant clauses in {@link KeyAst}.
 *
 * @author Alexander Weigl
 * @version 1 (12/4/19)
 */
public class ContractsAndInvariantsFinder extends ExpressionBuilder {
    private final DeclarationBuilder declarationBuilder;
    private final List<Contract> contracts = new ArrayList<>();
    private final List<ClassInvariant> invariants = new ArrayList<>();


    private ParsableVariable selfVar;

    public ContractsAndInvariantsFinder(Services services, NamespaceSet nss) {
        super(services, nss);
        declarationBuilder = new DeclarationBuilder(services, nss);
    }

    public @Nonnull List<Contract> getContracts() {
        return contracts;
    }

    public @Nonnull List<ClassInvariant> getInvariants() {
        return invariants;
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        mapOf(ctx.contracts());
        mapOf(ctx.invariants());
        return null;
    }

    @Override
    public Object visitContracts(KeYParser.ContractsContext ctx) {
        return mapOf(ctx.one_contract());
    }

    @Override
    public Object visitOne_contract(KeYParser.One_contractContext ctx) {
        String contractName = visitSimple_ident(ctx.contractName);
        // for program variable declarations
        Namespace<IProgramVariable> oldProgVars = namespaces().programVariables();
        namespaces().setProgramVariables(new Namespace<>(oldProgVars));
        declarationBuilder.visitProg_var_decls(ctx.prog_var_decls());
        Term fma = accept(ctx.fma);
        Term modifiesClause = accept(ctx.modifiesClause);
        DLSpecFactory dsf = new DLSpecFactory(getServices());
        try {
            FunctionalOperationContract dlOperationContract =
                dsf.createDLOperationContract(contractName, fma, modifiesClause);
            contracts.add(dlOperationContract);
        } catch (ProofInputException e) {
            semanticError(ctx, e.getMessage());
        }
        // dump local program variable declarations
        namespaces().setProgramVariables(oldProgVars);
        return null;
    }


    @Override
    public Object visitInvariants(KeYParser.InvariantsContext ctx) {
        Namespace<QuantifiableVariable> orig = variables();
        selfVar = (ParsableVariable) ctx.selfVar.accept(this);
        ctx.one_invariant().forEach(it -> it.accept(this));
        unbindVars(orig);
        return null;
    }

    @Override
    public Object visitOne_invariant(KeYParser.One_invariantContext ctx) {
        String invName = visitSimple_ident(ctx.simple_ident());
        Term fma = accept(ctx.fma);
        String displayName = ctx.displayName != null ? ctx.displayName.getText() : null;
        DLSpecFactory dsf = new DLSpecFactory(getServices());
        try {
            ClassInvariant inv = dsf.createDLClassInvariant(invName, displayName, selfVar, fma);
            invariants.add(inv);
        } catch (ProofInputException e) {
            semanticError(ctx, e.getMessage());
        }
        return null;
    }

}
