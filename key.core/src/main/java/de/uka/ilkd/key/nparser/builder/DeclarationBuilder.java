/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.logic.sort.ParametricSortDeclaration.SortParameter;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.rule.RuleSet;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.*;

import org.antlr.v4.runtime.Token;
import org.key_project.util.java.CollectionUtil;
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
        var name = ctx.name.getText();
        List<SortParameter> typeParameters = accept(ctx.formal_sort_parameters());
        var doc = ctx.DOC_COMMENT() != null
                ? ctx.DOC_COMMENT().getText()
                : null;
        var origin = BuilderHelpers.getPosition(ctx);
        if (typeParameters == null) {
            var s = new SortImpl(new Name(name), ImmutableSet.empty(), false, doc, origin);
            sorts().addSafely(s);
        } else {
            var tp = typeParameters.stream().map(SortParameter::genericSort)
                    .collect(ImmutableList.collector());
            var doubled = CollectionUtil.findDuplicates(tp);
            if (!doubled.isEmpty()) {
                semanticError(ctx.formal_sort_parameters(),
                    "Type parameters must be unique within a declaration. Found duplicate: %s", doubled.getFirst());
            }
            var variance =
                typeParameters.stream().map(SortParameter::variance)
                        .collect(ImmutableList.collector());
            var s = new ParametricSortDeclaration(
                new Name(name), ImmutableSet.empty(), false, tp, variance,
                doc, origin);
            namespaces().parametricSorts().add(s);
        }
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


    public record NamedFormalSortParameter(String name, List<SortParameter> parameters) {}

//    @Override
//    public List<NamedFormalSortParameter> visitSortList(KeYParser.SortListContext ctx) {
//        List<NamedFormalSortParameter> seq = new ArrayList<>();
//        for (KeYParser.SortIdContext context : ctx.sortId()) {
//            String sortName = context.simple_ident_dots().getText();
//            // String brackets = StringUtil.repeat("[]", context.EMPTYBRACKETS().size());
//            List<SortParameter> typeParams = accept(context.formal_sort_parameters());
//            seq.add(new NamedFormalSortParameter(sortName,
//                typeParams != null ? typeParams : Collections.emptyList()));
//        }
//        return seq;
//    }


    @Override
    public Object visitOne_sort_decl(KeYParser.One_sort_declContext ctx) {
        // List<Pair<String, List<Pair<ParametricSort.Variance, Sort>>>> sortIds =
        // accept(ctx.sortIds);
        List<Sort> sortOneOf = accept(ctx.sortOneOf);
        List<Sort> sortExt = accept(ctx.sortExt);
        boolean isGenericSort = ctx.GENERIC() != null;
        boolean isProxySort = ctx.PROXY() != null;
        boolean isAbstractSort = ctx.ABSTRACT() != null;
        List<Sort> createdSorts = new LinkedList<>();
        // assert sortIds != null;

        ImmutableSet<Sort> ext = sortExt == null ? ImmutableSet.empty()
                : Immutables.setOf(sortExt);
        ImmutableSet<Sort> oneOf = sortOneOf == null ? ImmutableSet.empty()
                : Immutables.setOf(sortOneOf);

        var documentation = ParsingFacade.getValueDocumentation(ctx.DOC_COMMENT());

        if(ctx.sortIds == null) {
            // parametrised sorts
            var declCtx = ctx.parametric_sort_decl();
            assert declCtx != null : "One of the two must be present";
            List<SortParameter> typeParams = mapOf(declCtx.formal_sort_param_decl());
            ImmutableList<SortParameter> params = Immutables.listOf(typeParams);
            var doubled = CollectionUtil.findDuplicates(params.map(SortParameter::genericSort));
            if (!doubled.isEmpty()) {
                semanticError(declCtx,
                        "Type parameters must be unique within a declaration. Found duplicate: %s", doubled.getFirst());
            }
            String name = declCtx.simple_ident_dots().getText();
            Name sortName = new Name(name);
            var sortDecl = new ParametricSortDeclaration(sortName, ext, isAbstractSort, params, documentation, BuilderHelpers.getPosition(declCtx));
            namespaces().parametricSorts().add(sortDecl);

        } else {
            for (var idCtx : ctx.sortIds.simple_ident_dots()) {
                var name = idCtx.getText();
                Name sortName = new Name(name);

                // attention: no expand to java.lang here!
                Sort existingSort = sorts().lookup(sortName);
                if (existingSort == null) {
                    Sort s = null;
                    if (isGenericSort) {
                        try {
                            s = new GenericSort(sortName, ext, oneOf, documentation,
                                    BuilderHelpers.getPosition(ctx));
                        } catch (GenericSupersortException e) {
                            semanticError(ctx, "Illegal sort given");
                        }
                    } else if (new Name("any").equals(sortName)) {
                        s = JavaDLTheory.ANY;
                    } else {
                        if (isProxySort) {
                            s = new ProxySort(sortName, ext, documentation,
                                    BuilderHelpers.getPosition(idCtx));
                        } else {
                            s = new SortImpl(sortName, ext, isAbstractSort,
                                    documentation, BuilderHelpers.getPosition(idCtx));
                        }
                    }
                    // parametric sort declarations are not sorts themselves.
                    assert s != null;
                    sorts().add(s);
                    createdSorts.add(s);
                } else {
                    // weigl: agreement on KaKeY meeting: this should be ignored until we finally have
                    // local namespaces for generic sorts
                    // addWarning(ctx, "Sort declaration is ignored, due to collision.");
                    LOGGER.debug("Sort declaration of {} in {} is ignored due to collision (already "
                                    + "present in {}).", sortName, BuilderHelpers.getPosition(ctx),
                            existingSort.getOrigin());
                }
            }
        }
        return createdSorts;
    }

    @Override
    public SortParameter visitFormal_sort_param_decl(KeYParser.Formal_sort_param_declContext ctx) {
        ParametricSortDeclaration.Variance variance;
        if (ctx.PLUS() != null)
            variance = ParametricSortDeclaration.Variance.COVARIANT;
        else if (ctx.MINUS() != null)
            variance = ParametricSortDeclaration.Variance.CONTRAVARIANT;
        else
            variance = ParametricSortDeclaration.Variance.INVARIANT;

        var name = ctx.simple_ident().getText();
        Sort paramSort = sorts().lookup(name);
        if(paramSort == null) {
            semanticError(ctx, "Parameter sort %s not found", name);
        }
        if(!(paramSort instanceof GenericSort)) {
            semanticError(ctx, "Parameter sort %s is not a generic sort", name);
        }

        return new SortParameter((GenericSort) paramSort, variance);
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
