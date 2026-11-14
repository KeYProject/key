/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser;

import java.nio.file.Paths;
import java.util.Objects;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class AliasTest {
    @Test
    public void intSeqTest() throws ProblemLoaderException {
        var path = Paths.get("../key.ui/examples/standard_key/polymorphic/pseq.key");
        var env = KeYEnvironment.load(path);

        var pSeq = Objects.requireNonNull(
            env.getInitConfig().namespaces().parametricSorts().lookup("PSeq"),
            "PSeq must be defined in the pseq.key example");
        var intSort = Objects.requireNonNull(
            env.getInitConfig().namespaces().lookupSortOrAlias("int"), "int must be defined");
        var intSeq = ParametricSortInstance.get(pSeq,
            ImmutableList.of(new GenericArgument(intSort)),
            env.getServices());
        Assertions.assertEquals(intSeq,
            env.getInitConfig().namespaces().lookupSortOrAlias("IntSeq"));
    }
}
