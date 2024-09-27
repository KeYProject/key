package org.key_project.ncore.rules;

import org.key_project.util.collection.ImmutableList;

public record AssumesMatchResult(ImmutableList<AssumesFormulaInstantiation> candidates, ImmutableList<MatchConditions> mcCandidates) {
}
