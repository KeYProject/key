/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.sort.GenericSort;
import org.key_project.rusty.logic.sort.SortImpl;
import org.key_project.rusty.parser.KeYRustyParser;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Immutables;

public class DeclarationBuilder extends DefaultBuilder {
    private final Map<String, String> category2Default = new HashMap<>();

    public DeclarationBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    @Override
    public Object visitDecls(KeYRustyParser.DeclsContext ctx) {
        mapMapOf(ctx.option_decls(), ctx.options_choice(), ctx.ruleset_decls(), ctx.sort_decls(),
            ctx.datatype_decls(),
            ctx.prog_var_decls(), ctx.schema_var_decls());
        return null;
    }

    @Override
    public Object visitDatatype_decl(KeYRustyParser.Datatype_declContext ctx) {
        // boolean freeAdt = ctx.FREE() != null;
        var name = ctx.name.getText();
        var s = new SortImpl(new Name(name), false);
        sorts().addSafely(s);
        return null;
    }

    @Override
    public Object visitProg_var_decls(KeYRustyParser.Prog_var_declsContext ctx) {
        for (int i = 0; i < ctx.simple_ident_comma_list().size(); i++) {
            List<String> varNames = accept(ctx.simple_ident_comma_list(i));
            /*
             * KeYJavaType kjt = accept(ctx.keyjavatype(i));
             * assert varNames != null;
             * for (String varName : varNames) {
             * if (varName.equals("null")) {
             * semanticError(ctx.simple_ident_comma_list(i),
             * "Function '" + varName + "' is already defined!");
             * }
             * ProgramElementName pvName = new ProgramElementName(varName);
             * Named name = lookup(pvName);
             * if (name != null) {
             * // commented out as pv do not have unique name (at the moment)
             * // throw new AmbigiousDeclException(varName, getSourceName(), getLine(),
             * // getColumn())
             * if (!(name instanceof ProgramVariable pv)
             * || !(pv).getKeYJavaType().equals(kjt)) {
             * programVariables().add(new LocationVariable(pvName, kjt));
             * }
             * } else {
             * programVariables().add(new LocationVariable(pvName, kjt));
             * }
             * }
             */
        }
        return null;
    }

    @Override
    public Object visitSort_decls(KeYRustyParser.Sort_declsContext ctx) {
        for (KeYRustyParser.One_sort_declContext c : ctx.one_sort_decl()) {
            c.accept(this);
        }
        return null;
    }

    @Override
    public Object visitOne_sort_decl(KeYRustyParser.One_sort_declContext ctx) {
        List<Sort> sortOneOf = accept(ctx.sortOneOf);
        List<Sort> sortExt = accept(ctx.sortExt);
        boolean isGenericSort = ctx.GENERIC() != null;
        boolean isAbstractSort = ctx.ABSTRACT() != null;
        List<Sort> createdSorts = new LinkedList<>();
        for (var idCtx : ctx.sortIds.simple_ident_dots()) {
            String sortId = accept(idCtx);
            Name sortName = new Name(sortId);

            ImmutableSet<Sort> ext = sortExt == null ? ImmutableSet.empty()
                    : Immutables.createSetFrom(sortExt);
            ImmutableSet<Sort> oneOf = sortOneOf == null ? ImmutableSet.empty()
                    : Immutables.createSetFrom(sortOneOf);

            // attention: no expand to java.lang here!
            Sort existingSort = sorts().lookup(sortName);
            if (existingSort == null) {
                Sort s = null;
                if (isGenericSort) {
                    var gs = new GenericSort(sortName, ext, oneOf);
                    s = gs;
                } else if (new Name("any").equals(sortName)) {
                    s = RustyDLTheory.ANY;
                } else {
                    s = new SortImpl(sortName, isAbstractSort, ext);
                }
                sorts().add(s);
                createdSorts.add(s);
            } else {
                // weigl: agreement on KaKeY meeting: this should be ignored until we finally have
                // local namespaces for generic sorts
                // addWarning(ctx, "Sort declaration is ignored, due to collision.");
                // LOGGER.info("Sort declaration of {} in {} is ignored due to collision (already "
                // + "present in {}).", sortName, BuilderHelpers.getPosition(ctx),
                // existingSort.getOrigin());
            }
        }
        return createdSorts;
    }

    @Override
    public List<Sort> visitOneof_sorts(KeYRustyParser.Oneof_sortsContext ctx) {
        return mapOf(ctx.sortId());
    }
}
