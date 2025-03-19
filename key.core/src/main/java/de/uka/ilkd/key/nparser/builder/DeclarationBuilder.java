/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.rule.RuleSet;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Immutables;

import org.antlr.v4.runtime.Token;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This visitor evaluates all basic (level 0) declarations. This includes:
 * <ul>
 * <li>Option Declarations</li>
 * <li>Sorts</li>
 * <li>Program variables</li>
 * <li>Schema variables</li>
 * <li>Rulesets</li>
 * </ul>
 * <p>
 * This information is registered into the given {@link NamespaceSet}.
 *
 * @author Alexander Weigl
 * @version 1 (12/4/19)
 * @see FunctionPredicateBuilder for level-1 declarations
 */
public class DeclarationBuilder extends DefaultBuilder {
    private final Map<String, String> category2Default = new HashMap<>();
    private static final Logger LOGGER = LoggerFactory.getLogger(DeclarationBuilder.class);

    public DeclarationBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        mapMapOf(ctx.option_decls(), ctx.options_choice(), ctx.ruleset_decls(), ctx.sort_decls(),
            ctx.datatype_decls(),
            ctx.prog_var_decls(), ctx.schema_var_decls());
        return null;
    }

    @Override
    public Object visitDatatype_decl(KeYParser.Datatype_declContext ctx) {
        // boolean freeAdt = ctx.FREE() != null;
        var name = ctx.name.getText();
        var doc = ctx.DOC_COMMENT() != null
                ? ctx.DOC_COMMENT().getText()
                : null;
        var origin = BuilderHelpers.getPosition(ctx);
        var s = new SortImpl(new Name(name), ImmutableSet.empty(), false, doc, origin);
        sorts().addSafely(s);
        return null;
    }

    @Override
    public Object visitProg_var_decls(KeYParser.Prog_var_declsContext ctx) {
        for (int i = 0; i < ctx.simple_ident_comma_list().size(); i++) {
            List<String> varNames = accept(ctx.simple_ident_comma_list(i));
            KeYJavaType kjt = accept(ctx.keyjavatype(i));
            assert varNames != null;
            for (String varName : varNames) {
                if (varName.equals("null")) {
                    semanticError(ctx.simple_ident_comma_list(i),
                        "Function '" + varName + "' is already defined!");
                }
                ProgramElementName pvName = new ProgramElementName(varName);
                Named name = lookup(pvName);
                if (name != null) {
                    // commented out as pv do not have unique name (at the moment)
                    // throw new AmbigiousDeclException(varName, getSourceName(), getLine(),
                    // getColumn())
                    if (!(name instanceof ProgramVariable)
                            || !((ProgramVariable) name).getKeYJavaType().equals(kjt)) {
                        programVariables().add(new LocationVariable(pvName, kjt));
                    }
                } else {
                    programVariables().add(new LocationVariable(pvName, kjt));
                }
            }
        }
        return null;
    }


    @Override
    public Object visitChoice(KeYParser.ChoiceContext ctx) {
        String cat = ctx.category.getText();
        for (KeYParser.OptionDeclContext optdecl : ctx.optionDecl()) {
            Token catctx = optdecl.IDENT;
            String name = cat + ":" + catctx.getText();
            Choice c = choices().lookup(new Name(name));
            if (c == null) {
                c = new Choice(catctx.getText(), cat);
                choices().add(c);
            }
            category2Default.putIfAbsent(cat, name);
        }
        category2Default.computeIfAbsent(cat, it -> {
            choices().add(new Choice("On", cat));
            choices().add(new Choice("Off", cat));
            return cat + ":On";
        });
        return null;
    }

    @Override
    public Object visitSort_decls(KeYParser.Sort_declsContext ctx) {
        for (KeYParser.One_sort_declContext c : ctx.one_sort_decl()) {
            c.accept(this);
        }
        return null;
    }

    @Override
    public Object visitOne_sort_decl(KeYParser.One_sort_declContext ctx) {
        List<Sort> sortOneOf = accept(ctx.sortOneOf);
        List<Sort> sortExt = accept(ctx.sortExt);
        boolean isGenericSort = ctx.GENERIC() != null;
        boolean isProxySort = ctx.PROXY() != null;
        boolean isAbstractSort = ctx.ABSTRACT() != null;
        List<Sort> createdSorts = new LinkedList<>();
        var documentation = ParsingFacade.getValueDocumentation(ctx.DOC_COMMENT());
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
                    try {
                        var gs = new GenericSort(sortName, ext, oneOf, documentation,
                            BuilderHelpers.getPosition(idCtx));
                        s = gs;
                    } catch (GenericSupersortException e) {
                        semanticError(ctx, "Illegal sort given");
                    }
                } else if (new Name("any").equals(sortName)) {
                    s = JavaDLTheory.ANY;
                } else {
                    if (isProxySort) {
                        var ps = new ProxySort(sortName, ext, documentation,
                            BuilderHelpers.getPosition(idCtx));
                        s = ps;
                    } else {
                        var si = new SortImpl(sortName, ext, isAbstractSort,
                            documentation, BuilderHelpers.getPosition(idCtx));
                        s = si;
                    }
                }
                assert s != null;
                sorts().add(s);
                createdSorts.add(s);
            } else {
                // weigl: agreement on KaKeY meeting: this should be ignored until we finally have
                // local namespaces for generic sorts
                // addWarning(ctx, "Sort declaration is ignored, due to collision.");
                LOGGER.info("Sort declaration of {} in {} is ignored due to collision (already "
                    + "present in {}).", sortName, BuilderHelpers.getPosition(ctx),
                    existingSort.getOrigin());
            }
        }
        return createdSorts;
    }

    @Override
    public Object visitOption_decls(KeYParser.Option_declsContext ctx) {
        return mapOf(ctx.choice());
    }

    @Override
    public List<Sort> visitExtends_sorts(KeYParser.Extends_sortsContext ctx) {
        return mapOf(ctx.sortId());
    }

    @Override
    public List<Sort> visitOneof_sorts(KeYParser.Oneof_sortsContext ctx) {
        return mapOf(ctx.sortId());
    }


    @Override
    public Object visitRuleset_decls(KeYParser.Ruleset_declsContext ctx) {
        for (String id : this.<String>mapOf(ctx.simple_ident())) {
            RuleSet h = new RuleSet(new Name(id));
            if (ruleSets().lookup(new Name(id)) == null) {
                ruleSets().add(h);
            }
        }
        return null;
    }


    @Override
    public Object visitOptions_choice(KeYParser.Options_choiceContext ctx) {
        return null;
    }


}
