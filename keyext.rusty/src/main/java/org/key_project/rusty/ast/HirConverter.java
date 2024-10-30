/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import java.util.Arrays;

import org.key_project.rusty.Services;
import org.key_project.util.collection.ImmutableList;

public class HirConverter {
    private final Services services;

    public HirConverter(Services services) {
        this.services = services;
    }

    public Services getServices() {
        return services;
    }

    public Crate convertCrate(org.key_project.rusty.parser.hir.Crate crate) {
        return new Crate(convertMod(crate.topMod()));
    }

    private Mod convertMod(org.key_project.rusty.parser.hir.Mod mod) {
        return new Mod(
            Arrays.stream(mod.items()).map(this::convertItem).collect(ImmutableList.collector()));
    }

    private Item convertItem(org.key_project.rusty.parser.hir.item.Item item) {
        return null;
    }


}
