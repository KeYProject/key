package org.keyproject.key.api.data;


import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (15.10.23)
 */
public record ProblemDefinition(
        @Nullable List<SortDesc> sorts,
        @Nullable List<FunctionDesc> functions,
        @Nullable List<PredicateDesc> predicates,
        @Nullable List<String> antecTerms,
        @Nullable List<String> succTerms
) {
}
