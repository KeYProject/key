package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import org.key_project.extsourceview.debug.tabs.OriginRefView;

import java.io.IOException;

public class InsertionTerm {
    public final InsertionType Type;
    public final de.uka.ilkd.key.logic.Term Term;

    public InsertionTerm(InsertionType type, de.uka.ilkd.key.logic.Term term) {
        Type = type;
        Term = term;
    }

    public boolean IsRevelant() {

        OriginRef orig = Term.getOriginRef();
        if (orig == null) return true;

        if (orig.Type == OriginRefType.IMPLICIT_ENSURES_EXCNULL) return false;
        if (orig.Type == OriginRefType.IMPLICIT_REQUIRES_SELFNOTNULL) return false;
        if (orig.Type == OriginRefType.IMPLICIT_REQUIRES_SELFCREATED) return false;
        if (orig.Type == OriginRefType.IMPLICIT_REQUIRES_SELFEXACTINSTANCE) return false;
        if (orig.Type == OriginRefType.IMPLICIT_REQUIRES_PARAMSOK) return false;
        if (orig.Type == OriginRefType.IMPLICIT_REQUIRES_MEASUREDBY_INITIAL) return false;
        if (orig.Type == OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP) return false;

        return true;
    }
}
