/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.GenericParameter;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.NamespaceBuilder;
import de.uka.ilkd.key.proof.init.AbstractProfile;

import org.key_project.logic.Name;
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
        this.services = new Services(AbstractProfile.getDefaultProfile());
        this.nss = services.getNamespaces();
        this.io = new KeyIO(services, nss);

        nss.sorts().add(g1 = new GenericSort(new Name("G1")));
        nss.sorts().add(new GenericSort(new Name("G2")));
        nss.sorts().add(new GenericSort(new Name("G3")));
        nss.sorts().add(new GenericSort(new Name("G4")));

        NamespaceBuilder nb = new NamespaceBuilder(nss);
        nb.addSort("boolean").addSort("int").addSort("Seq").addSort("LocSet").addSort("double")
                .addSort("float");

        Recoder2KeY r2k = new Recoder2KeY(services, nss);
        r2k.parseSpecialClasses();
    }

    private ParametricSortDecl addParametricSort(String name,
            GenericParameter.Variance... variance) {
        ImmutableList<GenericParameter> params = ImmutableList.of();
        for (int i = 0; i < variance.length; i++) {
            GenericParameter.Variance varia = variance[i];
            GenericSort genSort = (GenericSort) nss.sorts().lookup("G" + (i + 1));
            params = params.prepend(new GenericParameter(genSort, varia));
        }
        ParametricSortDecl psd = new ParametricSortDecl(new Name(name), false, ImmutableSet.empty(),
            params, "", "");
        nss.parametricSorts().add(psd);
        return psd;
    }


    @Test
    public void testParametricSortIdentical() {
        ParametricSortDecl psd = addParametricSort("List", GenericParameter.Variance.COVARIANT);
        var sdf = SortDependingFunction.createFirstInstance(g1, new Name("someConst"), g1,
            new Sort[0], false);
        nss.functions().add(sdf);

        var term = io.parseExpression("List<[int]>::someConst = List<[int]>::someConst");
        assertEquals(term.sub(0), term.sub(1));
        assertSame(term.sub(0).sort(), term.sub(1).sort());
    }

    @Test
    public void testParametricSortDependentFunctionInstantiation() {
        ParametricSortDecl psd = addParametricSort("List", GenericParameter.Variance.COVARIANT);
        Sort intSort = nss.sorts().lookup("int");

        var someConst = SortDependingFunction.createFirstInstance(g1, new Name("someConst"), g1,
            new Sort[0], false);
        nss.functions().add(someConst);

        var listOfInt =
            ParametricSortInstance.get(psd, ImmutableList.of(new GenericArgument(intSort)));
        var listOfG1 = ParametricSortInstance.get(psd, ImmutableList.of(new GenericArgument(g1)));
        var sdf = SortDependingFunction.createFirstInstance(g1, new Name("head"), g1,
            new Sort[] { listOfG1 }, false);
        nss.functions().add(sdf);

        SortDependingFunction sdfInst = sdf.getInstanceFor(intSort, services);
        assertEquals(intSort, sdfInst.sort());
        assertEquals(listOfInt, sdfInst.argSort(0));

        var term = io.parseExpression("int::head(List<[int]>::someConst) = int::someConst");
        assertEquals("List<[int]>", term.sub(0).sub(0).sort().toString());
        assertEquals("List<[int]>", ((JFunction) term.sub(0).op()).argSorts().get(0).toString());
        assertEquals("int", term.sub(0).op().sort(new Sort[0]).toString());
        assertSame(term.sub(0).sort(), term.sub(1).sort());
    }

    @Test
    public void testParametricFunctionInstantiation() {
        ParametricSortDecl psd = addParametricSort("List", GenericParameter.Variance.COVARIANT);
        Sort intSort = nss.sorts().lookup("int");

        var someConst = new ParametricFunctionDecl(new Name("someConst"),
            ImmutableList.of(new GenericParameter(g1, GenericParameter.Variance.COVARIANT)),
            new ImmutableArray<>(), g1, null, false, true, false);
        nss.parametricFunctions().add(someConst);

        var listOfInt =
            ParametricSortInstance.get(psd, ImmutableList.of(new GenericArgument(intSort)));
        var listOfG1 = ParametricSortInstance.get(psd, ImmutableList.of(new GenericArgument(g1)));

        var head = new ParametricFunctionDecl(new Name("head"),
            ImmutableList.of(new GenericParameter(g1, GenericParameter.Variance.COVARIANT)),
            new ImmutableArray<>(listOfG1), g1, null, false, true, false);
        nss.parametricFunctions().add(head);

        var headInst =
            ParametricFunctionInstance.get(head, ImmutableList.of(new GenericArgument(intSort)));
        assertEquals(intSort, headInst.sort());
        assertEquals(listOfInt, headInst.argSort(0));

        var term = io.parseExpression("head<[int]>(someConst<[List<[int]>]>) = someConst<[int]>");
        assertEquals("List<[int]>", term.sub(0).sub(0).sort().toString());
        assertEquals("List<[int]>", ((JFunction) term.sub(0).op()).argSorts().get(0).toString());
        assertEquals("int", term.sub(0).op().sort(new Sort[0]).toString());
        assertSame(term.sub(0).sort(), term.sub(1).sort());
    }
}
