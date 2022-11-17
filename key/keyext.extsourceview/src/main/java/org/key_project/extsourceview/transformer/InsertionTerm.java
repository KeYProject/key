package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import org.key_project.extsourceview.debug.tabs.OriginRefView;
import org.key_project.util.collection.ImmutableArray;

import java.io.IOException;

public class InsertionTerm {
    public final InsertionType Type;
    public final de.uka.ilkd.key.logic.Term Term;

    public InsertionTerm(InsertionType type, de.uka.ilkd.key.logic.Term term) {
        Type = type;
        Term = term;
    }

    public boolean IsRevelant() {

        ImmutableArray<OriginRef> orig = Term.getOriginRef();
        if (orig.isEmpty())
            return true;

        return !orig.stream().allMatch(p -> {
            if (p.Type == OriginRefType.IMPLICIT_ENSURES_EXCNULL)
                return true;
            if (p.Type == OriginRefType.IMPLICIT_REQUIRES_SELFNOTNULL)
                return true;
            if (p.Type == OriginRefType.IMPLICIT_REQUIRES_SELFCREATED)
                return true;
            if (p.Type == OriginRefType.IMPLICIT_REQUIRES_SELFEXACTINSTANCE)
                return true;
            if (p.Type == OriginRefType.IMPLICIT_REQUIRES_PARAMSOK)
                return true;
            if (p.Type == OriginRefType.IMPLICIT_REQUIRES_MEASUREDBY_INITIAL)
                return true;
            if (p.Type == OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP)
                return true;
            if (p.Type == OriginRefType.LOOP_INITIALLYVALID_WELLFORMED)
                return true;
            if (p.Type == OriginRefType.LOOP_BODYPRESERVEDINV_WELLFORMED)
                return true;
            if (p.Type == OriginRefType.LOOP_USECASE_WELLFORMED)
                return true;

            return false;
        });
    }
}
