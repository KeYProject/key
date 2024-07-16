/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser;

import java.util.LinkedList;
import java.util.List;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.parser.builder.DeclarationBuilder;
import org.key_project.rusty.parser.builder.FunctionPredicateBuilder;
import org.key_project.rusty.util.parsing.BuildingIssue;

import org.jspecify.annotations.NonNull;

public class KeYIO {
    private final Services services;
    private final NamespaceSet nss;
    private List<BuildingIssue> warnings = new LinkedList<>();

    public KeYIO(@NonNull Services services, @NonNull NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
    }

    public KeYIO(Services services) {
        this(services, services.getNamespaces());
    }

    /**
     * @param ctx
     * @return
     */
    public List<BuildingIssue> evalDeclarations(KeYAst.File ctx) {
        DeclarationBuilder declBuilder = new DeclarationBuilder(services, nss);
        ctx.accept(declBuilder);
        warnings.addAll(declBuilder.getBuildingIssues());
        return declBuilder.getBuildingIssues();
    }

    /**
     * @param ctx
     */
    public List<BuildingIssue> evalFuncAndPred(KeYAst.File ctx) {
        FunctionPredicateBuilder visitor = new FunctionPredicateBuilder(services, nss);
        ctx.accept(visitor);
        warnings.addAll(visitor.getBuildingIssues());
        return visitor.getBuildingIssues();
    }

    public List<BuildingIssue> getWarnings() {
        return warnings;
    }
}
