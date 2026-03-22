/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.GenericParameter;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.nparser.NamespaceBuilder;
import de.uka.ilkd.key.proof.init.AbstractProfile;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class TestAlias {
    private NamespaceSet nss;
    private Services services;

    @BeforeEach
    public void setUp() {
        this.services = new Services(AbstractProfile.getDefaultProfile());
        this.nss = services.getNamespaces();

        NamespaceBuilder nb = new NamespaceBuilder(nss);
        nb.addSort("boolean").addSort("int").addSort("Seq").addSort("LocSet").addSort("double")
                .addSort("float");

        Recoder2KeY r2k = new Recoder2KeY(services, nss);
        r2k.parseSpecialClasses();
    }

    private SortAlias addAlias(String name, String aliased) {
        var aliasedSort = nss.sorts().lookup(aliased);
        assert aliasedSort != null;
        var alias = new SortAlias(new Name(name), aliasedSort);
        nss.sortAliases().add(alias);
        return alias;
    }

    @Test
    public void testSimpleAlias() {
        var alias = addAlias("myInt", "int");
        assertEquals(alias.aliasedSort(), nss.lookupSortOrAlias("myInt"));
    }

    @Test
    public void testAliasOfParametric() {
        var pSet = new ParametricSortDecl(new Name("PSet"), false, ImmutableSet.empty(),
            ImmutableList.of(
                new GenericParameter(new GenericSort(new Name("A")),
                    GenericParameter.Variance.INVARIANT)),
            "");
        nss.parametricSorts().add(pSet);
        ParametricSortInstance intSet = ParametricSortInstance.get(pSet,
            ImmutableList.of(new GenericArgument(nss.lookupSortOrAlias("int"))), services);
        var alias = new SortAlias(new Name("IntSet"), intSet);
        nss.sortAliases().add(alias);
        assertEquals(intSet, nss.lookupSortOrAlias("IntSet"));
    }
}
