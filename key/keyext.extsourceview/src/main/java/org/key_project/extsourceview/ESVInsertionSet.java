package org.key_project.extsourceview;

import de.uka.ilkd.key.logic.Term;
import org.key_project.util.collection.ImmutableList;

public class ESVInsertionSet {
    public final ImmutableList<InsertionTerm> Assumes;
    public final ImmutableList<InsertionTerm> Asserts;

    public ESVInsertionSet(ImmutableList<InsertionTerm> assumes, ImmutableList<InsertionTerm> asserts) {
        Assumes = assumes;
        Asserts = asserts;
    }
}
