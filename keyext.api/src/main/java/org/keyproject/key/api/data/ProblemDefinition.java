/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;


import java.util.List;

import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (15.10.23)
 */
public record ProblemDefinition(
        @Nullable List<SortDesc> sorts,
        @Nullable List<FunctionDesc> functions,
        @Nullable List<PredicateDesc> predicates,
        @Nullable List<String> antecTerms,
        @Nullable List<String> succTerms) implements KeYDataTransferObject {
}
