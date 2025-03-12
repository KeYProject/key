@org.jetbrains.annotations.NotNull
/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
        package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.parser.SchemaVariableModifierSet;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import java.util.*;

import static de.uka.ilkd.key.ldt.JavaDLTheory.UPDATE;

/**
 * @author Alexander Weigl
 * @version 1 (27.02.25)
 */
@NullMarked
public record AdtHelper(Services services, Namespace<SchemaVariable> schemaVariables) {
    public AdtHelper(Services services) {
        this(services, new Namespace<>());
    }

    public static final class Adt {
        private final String package_;
        private final String name;
        private @Nullable Sort sort;
        private final List<AdtConstructor> constructors = new ArrayList<>();

        public Adt(String package_, String name) {
            this.name = name;
            this.package_ = package_;
        }

        public String name() {
            return name;
        }

        public @Nullable Sort sort() {
            return sort;
        }

        public List<AdtConstructor> constructors() {
            return constructors;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == this) return true;
            if (obj == null || obj.getClass() != this.getClass()) return false;
            var that = (Adt) obj;
            return Objects.equals(this.name, that.name) &&
                    Objects.equals(this.sort, that.sort) &&
                    Objects.equals(this.constructors, that.constructors);
        }

        @Override
        public int hashCode() {
            return Objects.hash(name, sort, constructors);
        }

        @Override
        public String toString() {
            return "Adt[" +
                    "name=" + name + ", " +
                    "sort=" + sort + ", " +
                    "constructors=" + constructors + ']';
        }

    }

    public static final class AdtConstructor {
        private final String name;
        private final List<String> sortNames = new ArrayList<>();
        private final List<String> argNames = new ArrayList<>();

        private final List<Sort> sorts = new ArrayList<>();

        public AdtConstructor(String name) {
            this.name = name;
        }

        public String name() {
            return name;
        }

        public List<String> argNames() {
            return argNames;
        }

        public List<String> sortNames() {
            return sortNames;
        }

        public List<Sort> sorts() {
            return sorts;
        }

        @Override
        public boolean equals(Object o) {
            if (o == null || getClass() != o.getClass()) return false;

            AdtConstructor that = (AdtConstructor) o;
            return name.equals(that.name) && sortNames.equals(that.sortNames) && argNames.equals(that.argNames) && sorts.equals(that.sorts);
        }

        @Override
        public int hashCode() {
            int result = name.hashCode();
            result = 31 * result + sortNames.hashCode();
            result = 31 * result + argNames.hashCode();
            result = 31 * result + sorts.hashCode();
            return result;
        }
    }

    public Sort createSort(String name, @Nullable String comment, @Nullable String origin) {
        var s = new SortImpl(new Name(name), ImmutableSet.empty(), false, comment, origin);
        sorts().addSafely(s);
        return s;
    }

    public void createConstructor(Sort sort, AdtConstructor c) {
        var dtNamespace = new Namespace<JFunction>();
        for (int i = 0; i < c.argNames.size(); i++) {
            var argSort = c.sorts.get(i);
            var argName = c.argNames.get(i);
            var alreadyDefinedFn = dtNamespace.lookup(argName);
            if (alreadyDefinedFn != null
                    && (!alreadyDefinedFn.sort().equals(argSort)
                    || !alreadyDefinedFn.argSort(0).equals(sort))) {
                throw new RuntimeException("Name already in namespace: " + argName);
            }
            var fn = new JFunction(new Name(argName), argSort, new Sort[]{sort}, null,
                    false, false);
            dtNamespace.add(fn);
        }
        final ImmutableArray<Sort> s = new ImmutableArray<>(c.argSort);
        var function = new JFunction(new Name(c.name), sort, s);
        functions().addSafely(function);
        functions().addSafely(dtNamespace.allElements());
    }

    public void createTaclets(Adt adt) {
        createAxiomTaclet(adt);
        createConstructorSplit(adt);
    }


    private RewriteTacletBuilder<RewriteTaclet> createAxiomTaclet(Adt adt) {
        var tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setName(new Name(String.format("%s_Axiom", adt.name)));
        var tb = services.getTermBuilder();
        var phi = declareSchemaVariable("phi", JavaDLTheory.FORMULA, true,
                new SchemaVariableModifierSet.FormulaSV());
        var qvar = (VariableSV) declareSchemaVariable("x", adt.sort,
                true,
                new SchemaVariableModifierSet.VariableSV());

        var find = tb.all(qvar, tb.var(phi)); // \forall #x #phi
        tacletBuilder.setFind(find);
        tacletBuilder.addVarsNotFreeIn(qvar, phi);

        var cases = adt.constructors.stream()
                .map(it -> createQuantifiedFormula(it, qvar, tb.var(phi), adt.sort))
                .toList();

        var axiom = tb.equals(find, tb.and(cases));

        var goal = new TacletGoalTemplate(
                Sequent.createAnteSequent(new Semisequent(new SequentFormula(axiom))),
                ImmutableSLList.nil());
        tacletBuilder.addTacletGoalTemplate(goal);

        tacletBuilder.setDisplayName("Axiom_for_" + adt.name);
        return tacletBuilder;
    }

    private Term createQuantifiedFormula(AdtConstructor c,
                                         QuantifiableVariable qvX, Term phi, Sort dt) {
        var tb = services.getTermBuilder();
        var fn = functions().lookup(c.name);
        var argSort = fn.argSorts();

        if (argSort.isEmpty()) {
            return tb.subst(qvX, tb.func(fn), phi);
        }

        var args = new Term[argSort.size()];
        var qvs = new ArrayList<QuantifiableVariable>(args.length);
        var ind = new ArrayList<Term>(args.length);

        for (int i = 0; i < argSort.size(); i++) {
            final var qv = new LogicVariable(new Name(c.argNames.get(i)), argSort.get(i));
            qvs.add(qv);
            args[i] = services.getTermFactory().createTerm(qvs.get(i));

            if (argSort.get(i).equals(dt)) {
                ind.add(tb.subst(qvX, args[i], phi));
            }
        }

        if (ind.isEmpty()) {
            return tb.all(qvs, tb.func(fn, args));
        } else {
            var base = tb.and(ind);
            return tb.all(qvs, tb.imp(base, tb.subst(qvX, tb.func(fn, args), phi)));
        }
    }

    private RewriteTacletBuilder<RewriteTaclet> createConstructorSplit(Adt adt) {
        final var tb = services.getTermBuilder();

        final String prefix = adt.name + "_";

        Map<String, Term> variables = new HashMap<>();
        for (AdtConstructor c : adt.constructors) {
            for (int i = 0; i < c.argNames.size(); i++) {
                var name = c.argNames.get(i);
                var sort = c.args.get(i);
                var sv = declareSchemaVariable(name, sort, true, new SchemaVariableModifierSet.TermSV());
                variables.put(name, tb.var(sv));
            }
        }

        final var b = new RewriteTacletBuilder<>();
        b.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        final var sort = adt.sort;

        b.setName(new Name(sort.name() + "_ctor_split"));
        b.setDisplayName("case distinction of " + sort.name());

        var phi = declareSchemaVariable("var", sort,
                false,
                new SchemaVariableModifierSet.TermSV());
        b.setFind(tb.var(phi));

        for (AdtConstructor c : adt.constructors) {
            var func = functions().lookup(adt.name);
            Term[] args = new Term[c.argNames.size()];
            for (int i = 0; i < args.length; i++) {
                args[i] = variables.get(c.argNames.get(i));
            }
            Semisequent antec =
                    new Semisequent(new SequentFormula(tb.equals(tb.var(phi), tb.func(func, args))));
            Sequent addedSeq = Sequent.createAnteSequent(antec);
            TacletGoalTemplate goal = new TacletGoalTemplate(addedSeq, ImmutableSLList.nil());
            goal.setName("#var = " + c.name);
            b.addTacletGoalTemplate(goal);
        }
        return b;
    }


    private Namespace<Sort> sorts() {
        return services.getNamespaces().sorts();
    }

    private Namespace<JFunction> functions() {
        return services.getNamespaces().functions();
    }


    private SchemaVariable declareSchemaVariable(String name, Sort s,
                                                 boolean makeSkolemTermSV,
                                                 SchemaVariableModifierSet mods) {
        SchemaVariable v;
        if (s == JavaDLTheory.FORMULA && !makeSkolemTermSV) {
            v = SchemaVariableFactory.createFormulaSV(new Name(name), mods.rigid());
        } else if (s == UPDATE) {
            v = SchemaVariableFactory.createUpdateSV(new Name(name));
        } else if (s instanceof ProgramSVSort) {
            v = SchemaVariableFactory.createProgramSV(new ProgramElementName(name),
                    (ProgramSVSort) s, mods.list());
        } else {
            if (false) {
                v = SchemaVariableFactory.createVariableSV(new Name(name), s);
            } else if (makeSkolemTermSV) {
                v = SchemaVariableFactory.createSkolemTermSV(new Name(name), s);
            } else if (false) {
                v = SchemaVariableFactory.createTermLabelSV(new Name(name));
            } else {
                v = SchemaVariableFactory.createTermSV(new Name(name), s, mods.rigid(),
                        mods.strict());
            }
        }

        if (services.getNamespaces().variables().lookup(v.name()) != null) {
            throw new RuntimeException("Schema variables shadows previous declared variable: " + v.name());
        }

        if (schemaVariables.lookup(v.name()) != null) {
            SchemaVariable old = schemaVariables().lookup(v.name());
            if (!old.sort().equals(v.sort())) {
                throw new RuntimeException("Schema variables clashes with previous declared schema variable: " + v.name());
            }
        }
        schemaVariables().add(v);
        return v;
    }

}
