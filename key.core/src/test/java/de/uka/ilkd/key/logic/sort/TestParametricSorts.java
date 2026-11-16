/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic.sort;

import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.GenericParameter;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.NamespaceBuilder;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class TestParametricSorts {
    private NamespaceSet nss;
    private Services services;
    private KeyIO io;
    private GenericSort g1;

    @BeforeEach
    public void setUp() {
        services = TacletForTests.services();
        services.getJavaService().parseSpecialClasses(null);
        nss = services.getNamespaces();
        io = new KeyIO(services, nss);

        nss.setSorts(new Namespace<>()); // fresh sorts
        nss.sorts().add(g1 = new GenericSort(new Name("G1")));
        nss.sorts().add(new GenericSort(new Name("G2")));
        nss.sorts().add(new GenericSort(new Name("G3")));
        nss.sorts().add(new GenericSort(new Name("G4")));

        NamespaceBuilder nb = new NamespaceBuilder(nss);
        nb.addSort("boolean").addSort("int")
                .addSort("Seq").addSort("LocSet").addSort("double")
                .addSort("float");
        nss.sorts().add(JavaDLTheory.ANY);
    }

    private ParametricSortDecl addParametricSort(String name,
            GenericParameter.Variance... variance) {
        ImmutableList<GenericParameter> params = ImmutableList.of();
        for (int i = 0; i < variance.length; i++) {
            GenericParameter.Variance varia = variance[i];
            Sort lookedUp = Objects
                    .requireNonNull(nss.sorts().lookup("G" + (i + 1)), "sort G" + (i + 1));
            GenericSort genSort = (GenericSort) lookedUp;
            params = params.prepend(new GenericParameter(genSort, varia));
        }
        ParametricSortDecl psd =
            new ParametricSortDecl(new Name(name), false, ImmutableSet.empty(), params);
        nss.parametricSorts().add(psd);
        return psd;
    }

    @Test
    public void testParametricFunctionInstantiation() {
        ParametricSortDecl psd = addParametricSort("List", GenericParameter.Variance.COVARIANT);
        Sort intSort = Objects.requireNonNull(nss.sorts().lookup("int"), "int must be declared");

        var someConst = new ParametricFunctionDecl(new Name("someConst"),
            ImmutableList.of(new GenericParameter(g1, GenericParameter.Variance.INVARIANT)),
            new ImmutableArray<>(), g1, null, false, true, false);
        nss.parametricFunctions().add(someConst);

        var listOfInt =
            ParametricSortInstance.get(psd, ImmutableList.of(new GenericArgument(intSort)),
                services);
        var listOfG1 =
            ParametricSortInstance.get(psd, ImmutableList.of(new GenericArgument(g1)), services);

        var head = new ParametricFunctionDecl(new Name("head"),
            ImmutableList.of(new GenericParameter(g1, GenericParameter.Variance.INVARIANT)),
            new ImmutableArray<>(listOfG1), g1, null, false, true, false);
        nss.parametricFunctions().add(head);

        var headInst =
            ParametricFunctionInstance.get(head, ImmutableList.of(new GenericArgument(intSort)),
                services);
        assertEquals(intSort, headInst.sort());
        assertEquals(listOfInt, headInst.argSort(0));

        var term = io.parseExpression("head<int>(someConst<List<int> >) = someConst<int>");
        assertEquals("List<int>", term.sub(0).sub(0).sort().toString());
        assertEquals("List<int>", ((JFunction) term.sub(0).op()).argSorts().get(0).toString());
        assertEquals("int", term.sub(0).op().sort(new Sort[0]).toString());
        assertSame(term.sub(0).sort(), term.sub(1).sort());
    }

    @Test
    public void testCovariance() {
        ParametricSortDecl psd = addParametricSort("List", GenericParameter.Variance.COVARIANT);
        Sort intSort = Objects.requireNonNull(nss.sorts().lookup("int"), "int must be declared");
        Sort anySort = Objects.requireNonNull(nss.sorts().lookup("any"), "any must be declared");

        var intList = ParametricSortInstance.get(psd,
            ImmutableList.of(new GenericArgument(intSort)), services);
        var anyList = ParametricSortInstance.get(psd,
            ImmutableList.of(new GenericArgument(anySort)), services);

        assertTrue(intList.extendsTrans(anyList));
        assertFalse(anyList.extendsTrans(intList));
    }

    @Test
    public void testContravariance() {
        ParametricSortDecl psd = addParametricSort("List", GenericParameter.Variance.CONTRAVARIANT);
        Sort intSort = Objects.requireNonNull(nss.sorts().lookup("int"), "int must be declared");
        Sort anySort = Objects.requireNonNull(nss.sorts().lookup("any"), "any must be declared");

        var intList = ParametricSortInstance.get(psd,
            ImmutableList.of(new GenericArgument(intSort)), services);
        var anyList = ParametricSortInstance.get(psd,
            ImmutableList.of(new GenericArgument(anySort)), services);

        assertFalse(intList.extendsTrans(anyList));
        assertTrue(anyList.extendsTrans(intList));
    }
}
