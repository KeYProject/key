/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.io.File;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.GenericParameter;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static de.uka.ilkd.key.rule.MatchConditions.EMPTY_MATCHCONDITIONS;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Pins the interning of {@link ParametricFunctionInstance}: {@code get} returns one shared
 * instance for value-equal (declaration, arguments) requests. The find-matcher relies on this —
 * a concrete generic argument is matched by reference identity, which is complete exactly because
 * a source operator with the same concrete arguments is the same object as the pattern's and thus
 * shares its {@link GenericArgument}s. If interning is weakened or removed, these tests fail
 * before the matcher starts to silently reject taclet applications.
 */
public class ParametricFunctionInterningTest {

    private Services services;
    private Sort concrete;
    private Sort concrete2;

    @BeforeEach
    public void setUp() {
        File ruleFile = new File(
            HelperClassForTests.TESTCASE_DIRECTORY + "/../de/uka/ilkd/key/rule/testRuleMatch.txt");
        TacletForTests.setStandardFile(ruleFile.getAbsolutePath());
        TacletForTests.parse();
        services = TacletForTests.services();
        concrete = TacletForTests.sortLookup("testSort");
        concrete2 = TacletForTests.sortLookup("nat");
    }

    /** a fresh parametric function declaration {@code name<A, ...>} without term arguments. */
    private ParametricFunctionDecl newDecl(String name, int parameterCount) {
        ImmutableList<GenericParameter> params = ImmutableList.nil();
        for (int i = parameterCount - 1; i >= 0; i--) {
            params = params.prepend(new GenericParameter(
                new GenericSort(new Name(name + "_P" + i)),
                GenericParameter.Variance.INVARIANT));
        }
        return new ParametricFunctionDecl(new Name(name), params, new ImmutableArray<>(),
            concrete, null, false, true, false);
    }

    @Test
    public void testEqualInstancesInternToOneObject() {
        final ParametricFunctionDecl decl = newDecl("internF", 2);
        final ParametricFunctionInstance first = ParametricFunctionInstance.get(decl,
            ImmutableList.of(new GenericArgument(concrete), new GenericArgument(concrete2)),
            services);
        final ParametricFunctionInstance second = ParametricFunctionInstance.get(decl,
            ImmutableList.of(new GenericArgument(concrete), new GenericArgument(concrete2)),
            services);

        assertSame(first, second,
            "value-equal parametric function instances must intern to one object");
        assertSame(first.getChild(0), second.getChild(0),
            "an interned instance shares its argument objects");
        assertSame(first.getChild(1), second.getChild(1),
            "an interned instance shares its argument objects");
    }

    @Test
    public void testMatcherMatchesIndependentlyBuiltConcreteInstance() {
        final ParametricFunctionDecl decl = newDecl("internG", 1);
        // pattern and source are built independently, as a taclet's find pattern and a sequent
        // formula are; the concrete-argument identity match succeeds through the interning
        final JTerm pattern = services.getTermBuilder().func(ParametricFunctionInstance.get(decl,
            ImmutableList.of(new GenericArgument(concrete)), services));
        final JTerm source = services.getTermBuilder().func(ParametricFunctionInstance.get(decl,
            ImmutableList.of(new GenericArgument(concrete)), services));

        final MatchResultInfo mc = JavaMatchPlanBuilder.compiledProgram(pattern)
                .match(source, EMPTY_MATCHCONDITIONS, services);
        assertNotNull(mc, "a concrete parametric function instance must match an independently"
            + " built equal one");
    }
}
