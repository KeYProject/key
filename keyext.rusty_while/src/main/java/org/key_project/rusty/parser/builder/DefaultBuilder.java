/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Namespace;
import org.key_project.logic.ParsableVariable;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.ty.KeYRustyType;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.parser.KeYRustyParser;

import org.jspecify.annotations.NonNull;

public class DefaultBuilder extends AbstractBuilder<Object> {
    protected final Services services;
    protected final NamespaceSet nss;
    private Namespace<SchemaVariable> schemaVariablesNamespace = new Namespace<>();


    public DefaultBuilder(Services services, NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
    }

    protected Named lookup(Name n) {
        final Namespace<?>[] lookups =
            { programVariables(), variables(), functions() };
        return doLookup(n, lookups);
    }

    protected <T> T doLookup(Name n, Namespace<?>... lookups) {
        for (Namespace<?> lookup : lookups) {
            Object l;
            if (lookup != null && (l = lookup.lookup(n)) != null) {
                try {
                    return (T) l;
                } catch (ClassCastException e) {
                }
            }
        }
        return null;
    }

    public NamespaceSet namespaces() {
        return nss;
    }

    protected Namespace<@NonNull QuantifiableVariable> variables() {
        return namespaces().variables();
    }

    protected Namespace<Sort> sorts() {
        return namespaces().sorts();
    }

    protected Namespace<Function> functions() {
        return namespaces().functions();
    }

    protected Namespace<ProgramVariable> programVariables() {
        return namespaces().programVariables();
    }

    public String visitSimple_ident_dots(KeYRustyParser.Simple_ident_dotsContext ctx) {
        return ctx.getText();
    }

    public List<Sort> visitArg_sorts_or_formula(KeYRustyParser.Arg_sorts_or_formulaContext ctx) {
        return mapOf(ctx.arg_sorts_or_formula_helper());
    }

    public Sort visitArg_sorts_or_formula_helper(
            KeYRustyParser.Arg_sorts_or_formula_helperContext ctx) {
        if (ctx.FORMULA() != null) {
            return RustyDLTheory.FORMULA;
        } else {
            return accept(ctx.sortId());
        }
    }

    /**
     * looks up and returns the sort of the given name or null if none has been found. If the sort
     * is not found for the first time, the name is expanded with "java.lang." and the look up
     * restarts
     */
    protected Sort lookupSort(String name) {
        return sorts().lookup(new Name(name));
    }

    public String visitString_value(KeYRustyParser.String_valueContext ctx) {
        return ctx.getText().substring(1, ctx.getText().length() - 1);
    }

    public Services getServices() {
        return services;
    }

    public Namespace<SchemaVariable> schemaVariables() {
        return schemaVariablesNamespace;
    }

    @Override
    public Object visitVarIds(KeYRustyParser.VarIdsContext ctx) {
        Collection<String> ids = accept(ctx.simple_ident_comma_list());
        List<ParsableVariable> list = new ArrayList<>(ids.size());
        for (String id : ids) {
            ParsableVariable v = (ParsableVariable) lookup(new Name(id));
            if (v == null) {
                semanticError(ctx, "Variable " + id + " not declared.");
            }
            list.add(v);
        }
        return list;
    }

    @Override
    public Object visitSimple_ident_dots_comma_list(
            KeYRustyParser.Simple_ident_dots_comma_listContext ctx) {
        return mapOf(ctx.simple_ident_dots());
    }

    @Override
    public String visitSimple_ident(KeYRustyParser.Simple_identContext ctx) {
        return ctx.IDENT().getText();
    }

    @Override
    public List<String> visitSimple_ident_comma_list(
            KeYRustyParser.Simple_ident_comma_listContext ctx) {
        return mapOf(ctx.simple_ident());
    }

    @Override
    public List<Boolean> visitWhere_to_bind(KeYRustyParser.Where_to_bindContext ctx) {
        List<Boolean> list = new ArrayList<>(ctx.children.size());
        ctx.b.forEach(it -> list.add(it.getText().equalsIgnoreCase("true")));
        return list;
    }

    @Override
    public List<Sort> visitArg_sorts(KeYRustyParser.Arg_sortsContext ctx) {
        return mapOf(ctx.sortId());
    }

    @Override
    public Sort visitSortId(KeYRustyParser.SortIdContext ctx) {
        return lookupSort(ctx.id.getText());
    }

    public KeYRustyType visitTypemapping(KeYRustyParser.TypemappingContext ctx) {
        StringBuilder type = new StringBuilder(visitSimple_ident_dots(ctx.simple_ident_dots()));
        Sort sort = lookupSort(type.toString());
        KeYRustyType krt = null;
        if (sort != null) {
            krt = new KeYRustyType(null, sort);
        }

        if (krt == null) {
            semanticError(ctx, "Unknown type: " + type);
        }

        return krt;
    }

    public Object visitFuncpred_name(KeYRustyParser.Funcpred_nameContext ctx) {
        return ctx.getText();
    }

}
