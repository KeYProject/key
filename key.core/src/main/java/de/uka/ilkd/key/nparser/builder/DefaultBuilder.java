/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.ResourceBundle;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.util.Pair;

import org.antlr.v4.runtime.ParserRuleContext;

/**
 * Helper class for are visitor that requires a namespaces and services. Also it provides the
 * evaluation of some basic {@link ParserRuleContext}s. This builder provides lookup functions for
 * the namespace set and also namespace for {@link SchemaVariable}. But it does not evaluate
 * schemaVariables, or other declarations.
 *
 * @author weigl
 * @version 1
 */
public class DefaultBuilder extends AbstractBuilder<Object> {
    public static final String LIMIT_SUFFIX = "$lmtd";

    private static final ResourceBundle bundle =
        ResourceBundle.getBundle("de.uka.ilkd.key.nparser.builder.resources");

    protected final Services services;
    protected final NamespaceSet nss;

    private Namespace<SchemaVariable> schemaVariablesNamespace = new Namespace<>();

    public DefaultBuilder(Services services, NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
    }

    @Override
    public List<String> visitPvset(KeYParser.PvsetContext ctx) {
        return mapOf(ctx.varId());
    }

    @Override
    public List<RuleSet> visitRulesets(KeYParser.RulesetsContext ctx) {
        return mapOf(ctx.ruleset());
    }

    @Override
    public RuleSet visitRuleset(KeYParser.RulesetContext ctx) {
        String id = ctx.IDENT().getText();
        RuleSet h = ruleSets().lookup(new Name(id));
        if (h == null) {
            h = new RuleSet(new Name(id));
            ruleSets().add(h);
            addWarning(ctx, String.format("Rule set %s was not previous defined.", ctx.getText()));
        }
        return h;
    }

    @Override
    public String visitSimple_ident_dots(KeYParser.Simple_ident_dotsContext ctx) {
        return ctx.getText();
    }

    protected Named lookup(Name n) {
        final Namespace<?>[] lookups =
            { programVariables(), variables(), schemaVariables(), functions() };
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

    protected void unbindVars(Namespace<QuantifiableVariable> orig) {
        namespaces().setVariables(orig);
    }

    /*
     * @Override public Integer visitLocation_ident(KeYParser.Location_identContext ctx) { var id =
     * accept(ctx.simple_ident()); if ("Location".equals(id)) { return LOCATION_MODIFIER; } else if
     * (!"Location".equals(id)) { semanticError(ctx,
     * "%s Attribute of a Non Rigid Function can only be 'Location'", id); } return NORMAL_NONRIGID;
     * }
     */

    @Override
    public List<Sort> visitArg_sorts_or_formula(KeYParser.Arg_sorts_or_formulaContext ctx) {
        return mapOf(ctx.arg_sorts_or_formula_helper());
    }

    @Override
    public Sort visitArg_sorts_or_formula_helper(KeYParser.Arg_sorts_or_formula_helperContext ctx) {
        if (ctx.FORMULA() != null) {
            return Sort.FORMULA;
        } else {
            return accept(ctx.sortId());
        }
    }

    /*
     * @Override public Sort visitAny_sortId(KeYParser.Any_sortIdContext ctx) { Pair<Sort, Type> p =
     * accept(ctx.any_sortId_help()); return toArraySort(p, ctx.EMPTYBRACKETS().size()); }
     */

    /**
     * looks up a function, (program) variable or static query of the given name varfunc_id and the
     * argument terms args in the namespaces and java info.
     *
     * @param varfuncName the String with the symbols name
     */
    protected Operator lookupVarfuncId(ParserRuleContext ctx, String varfuncName, String sortName,
            Sort sort) {
        Name name = new Name(varfuncName);
        Operator[] operators =
            new Operator[] { schemaVariables().lookup(name), variables().lookup(name),
                programVariables().lookup(new ProgramElementName(varfuncName)),
                functions().lookup(name), AbstractTermTransformer.name2metaop(varfuncName),

            };

        for (Operator op : operators) {
            if (op != null) {
                return op;
            }
        }

        if (sort != null || sortName != null) {
            Name fqName =
                new Name((sort != null ? sort.toString() : sortName) + "::" + varfuncName);
            operators =
                new Operator[] { schemaVariables().lookup(fqName), variables().lookup(fqName),
                    programVariables().lookup(new ProgramElementName(fqName.toString())),
                    functions().lookup(fqName),
                    AbstractTermTransformer.name2metaop(fqName.toString()) };

            for (Operator op : operators) {
                if (op != null) {
                    return op;
                }
            }

            SortDependingFunction firstInstance =
                SortDependingFunction.getFirstInstance(new Name(varfuncName), getServices());
            if (firstInstance != null) {
                SortDependingFunction v = firstInstance.getInstanceFor(sort, getServices());
                if (v != null) {
                    return v;
                }
            }
        }
        semanticError(ctx, "Could not find (program) variable or constant %s", varfuncName);
        return null;
    }

    public Sort toArraySort(Pair<Sort, Type> p, int numOfDimensions) {
        if (numOfDimensions != 0) {
            final JavaInfo ji = getJavaInfo();
            Sort sort = ArraySort.getArraySortForDim(p.first, p.second, numOfDimensions,
                ji.objectSort(), ji.cloneableSort(), ji.serializableSort());
            Sort s = sort;
            do {
                final ArraySort as = (ArraySort) s;
                sorts().add(as);
                s = as.elementSort();
            } while (s instanceof ArraySort && sorts().lookup(s.name()) == null);
            return sort;
        } else {
            return p.first;
        }
    }

    /**
     * looks up and returns the sort of the given name or null if none has been found. If the sort
     * is not found for the first time, the name is expanded with "java.lang." and the look up
     * restarts
     */
    protected Sort lookupSort(String name) {
        Sort result = sorts().lookup(new Name(name));
        if (result == null) {
            if (name.equals(NullSort.NAME.toString())) {
                Sort objectSort = sorts().lookup(new Name("java.lang.Object"));
                if (objectSort == null) {
                    semanticError(null,
                        "Null sort cannot be used before java.lang.Object is declared");
                }
                result = new NullSort(objectSort);
                sorts().add(result);
            } else {
                result = sorts().lookup(new Name("java.lang." + name));
            }
        }
        return result;
    }

    public NamespaceSet namespaces() {
        return nss;
    }

    protected Namespace<Sort> sorts() {
        return namespaces().sorts();
    }

    protected Namespace<Function> functions() {
        return namespaces().functions();
    }

    protected Namespace<RuleSet> ruleSets() {
        return namespaces().ruleSets();
    }

    protected Namespace<QuantifiableVariable> variables() {
        return namespaces().variables();
    }

    protected Namespace<IProgramVariable> programVariables() {
        return namespaces().programVariables();
    }

    protected Namespace<Choice> choices() {
        return namespaces().choices();
    }

    @Override
    public String visitString_value(KeYParser.String_valueContext ctx) {
        return ctx.getText().substring(1, ctx.getText().length() - 1);
    }

    public JavaInfo getJavaInfo() {
        return getServices().getJavaInfo();
    }

    public Services getServices() {
        return services;
    }

    public Namespace<SchemaVariable> schemaVariables() {
        return schemaVariablesNamespace;
    }

    public void setSchemaVariables(Namespace<SchemaVariable> ns) {
        this.schemaVariablesNamespace = ns;
    }

    @Override
    public Object visitVarIds(KeYParser.VarIdsContext ctx) {
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
            KeYParser.Simple_ident_dots_comma_listContext ctx) {
        return mapOf(ctx.simple_ident_dots());
    }

    @Override
    public String visitSimple_ident(KeYParser.Simple_identContext ctx) {
        return ctx.IDENT().getText();
    }

    @Override
    public List<String> visitSimple_ident_comma_list(KeYParser.Simple_ident_comma_listContext ctx) {
        return mapOf(ctx.simple_ident());
    }

    @Override
    public List<Boolean> visitWhere_to_bind(KeYParser.Where_to_bindContext ctx) {
        List<Boolean> list = new ArrayList<>(ctx.children.size());
        ctx.b.forEach(it -> list.add(it.getText().equalsIgnoreCase("true")));
        return list;
    }

    @Override
    public List<Sort> visitArg_sorts(KeYParser.Arg_sortsContext ctx) {
        return mapOf(ctx.sortId());
    }

    @Override
    public Sort visitSortId(KeYParser.SortIdContext ctx) {
        String primitiveName = ctx.id.getText();
        // Special handling for byte, char, short, long:
        // these are *not* sorts, but they are nevertheless valid
        // prefixes for array sorts such as byte[], char[][][].
        // Thus, we consider them aliases for the "int" sort, and remember
        // the corresponding Java type for the case that an array sort
        // is being declared.
        Type t = null;
        if (primitiveName.equals(PrimitiveType.JAVA_BYTE.getName())) {
            t = PrimitiveType.JAVA_BYTE;
            primitiveName = PrimitiveType.JAVA_INT.getName();
        } else if (primitiveName.equals(PrimitiveType.JAVA_CHAR.getName())) {
            t = PrimitiveType.JAVA_CHAR;
            primitiveName = PrimitiveType.JAVA_INT.getName();
        } else if (primitiveName.equals(PrimitiveType.JAVA_SHORT.getName())) {
            t = PrimitiveType.JAVA_SHORT;
            primitiveName = PrimitiveType.JAVA_INT.getName();
        } else if (primitiveName.equals(PrimitiveType.JAVA_INT.getName())) {
            t = PrimitiveType.JAVA_INT;
            primitiveName = PrimitiveType.JAVA_INT.getName();
        } else if (primitiveName.equals(PrimitiveType.JAVA_LONG.getName())) {
            t = PrimitiveType.JAVA_LONG;
            primitiveName = PrimitiveType.JAVA_INT.getName();
        } else if (primitiveName.equals(PrimitiveType.JAVA_BIGINT.getName())) {
            t = PrimitiveType.JAVA_BIGINT;
            primitiveName = PrimitiveType.JAVA_BIGINT.getName();
        }
        Sort s = lookupSort(primitiveName);
        if (s == null) {
            semanticError(ctx, "Could not find sort: %s", ctx.getText());
        }

        if (!ctx.EMPTYBRACKETS().isEmpty()) {
            return toArraySort(new Pair<>(s, t), ctx.EMPTYBRACKETS().size());
        }
        return s;
    }

    @Override
    public KeYJavaType visitKeyjavatype(KeYParser.KeyjavatypeContext ctx) {
        boolean array = false;
        StringBuilder type = new StringBuilder(visitSimple_ident_dots(ctx.simple_ident_dots()));
        for (int i = 0; i < ctx.EMPTYBRACKETS().size(); i++) {
            array = true;
            type.append("[]");
        }
        KeYJavaType kjt = getJavaInfo().getKeYJavaType(type.toString());

        // expand to "java.lang"
        if (kjt == null) {
            try {
                String guess = "java.lang." + type;
                kjt = getJavaInfo().getKeYJavaType(guess);
            } catch (Exception ignored) {
            }
        }

        // arrays
        if (kjt == null && array) {
            try {
                JavaBlock jb = getJavaInfo().readJavaBlock("{" + type + " k;}");
                kjt = ((VariableDeclaration) ((StatementBlock) jb.program()).getChildAt(0))
                        .getTypeReference().getKeYJavaType();
            } catch (Exception ignored) {
            }
        }

        // try as sort without Java type (neede e.g. for "Heap")
        if (kjt == null) {
            Sort sort = lookupSort(type.toString());
            if (sort != null) {
                kjt = new KeYJavaType(null, sort);
            }
        }

        if (kjt == null) {
            semanticError(ctx, "Unknown type: " + type);
        }

        return kjt;
    }

    @Override
    public Object visitFuncpred_name(KeYParser.Funcpred_nameContext ctx) {
        return ctx.getText();
    }
}
