package org.key_project.extsourceview.transformer;

import org.key_project.util.collection.ImmutableList;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class InsertionSet {
    public final ImmutableList<InsertionTerm> Insertions;

    public InsertionSet(ImmutableList<InsertionTerm> ins) {
        Insertions = ins;
    }

    public List<InsertionTerm> get(InsertionType... types) {
        return Insertions.stream().filter(p -> Arrays.stream(types).anyMatch(q -> p.Type == q)).collect(Collectors.toList());
    }
}
