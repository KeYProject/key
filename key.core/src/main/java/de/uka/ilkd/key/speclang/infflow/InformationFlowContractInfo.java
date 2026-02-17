/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.infflow;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (8/3/25)
 */
public record InformationFlowContractInfo(String informationFlowContractBasename,
        KeYJavaType forClass,
        IProgramMethod pm,
        KeYJavaType specifiedIn,
        JModality.JavaModalityKind modalityKind,
        JTerm requires, JTerm requiresFree, JTerm measuredBy, JTerm modifiable,
        boolean hasModifiable, @Nullable JTerm self, ImmutableList<JTerm> params,
        @Nullable JTerm result,
        @Nullable JTerm exc, JTerm atPre, JTerm accessible,
        ImmutableList<InfFlowSpec> infFlowSpecs,
        boolean toBeSaved) {
}
