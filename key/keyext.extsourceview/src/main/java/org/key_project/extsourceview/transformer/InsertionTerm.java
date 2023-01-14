package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import de.uka.ilkd.key.pp.PosInSequent;
import org.key_project.extsourceview.debug.tabs.OriginRefView;
import org.key_project.util.collection.ImmutableArray;

import java.io.IOException;

/**
 * This class represents a single InsertionTerm that will be spliced in the SourceView
 */
public class InsertionTerm {
    public final InsertionType Type;
    public final de.uka.ilkd.key.logic.Term Term;
    public final PosInOccurrence PIO;

    public InsertionTerm(InsertionType type, de.uka.ilkd.key.logic.Term term, PosInOccurrence pio) {
        Type = type;
        Term = term;
        PIO  = pio;
    }

    public boolean IsRevelant() {

        ImmutableArray<OriginRef> orig = Term.getOriginRef();
        if (orig.isEmpty())
            return true;

        return !orig.stream().allMatch(p -> isIrrelevantOriginRefType(p.Type));
    }

    public static boolean isIrrelevantOriginRefType(OriginRefType reftype) {
        if (reftype == OriginRefType.IMPLICIT_ENSURES_EXCNULL)
            return true;
        if (reftype == OriginRefType.IMPLICIT_REQUIRES_SELFNOTNULL)
            return true;
        if (reftype == OriginRefType.IMPLICIT_REQUIRES_SELFCREATED)
            return true;
        if (reftype == OriginRefType.IMPLICIT_REQUIRES_SELFEXACTINSTANCE)
            return true;
        if (reftype == OriginRefType.IMPLICIT_REQUIRES_PARAMSOK)
            return true;
        if (reftype == OriginRefType.IMPLICIT_REQUIRES_MEASUREDBY_INITIAL)
            return true;
        if (reftype == OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP)
            return true;
        if (reftype == OriginRefType.LOOP_INITIALLYVALID_WELLFORMED)
            return true;
        if (reftype == OriginRefType.LOOP_BODYPRESERVEDINV_WELLFORMED)
            return true;
        if (reftype == OriginRefType.LOOP_USECASE_WELLFORMED)
            return true;
        if (reftype == OriginRefType.OPERATION_PRE_WELLFORMED)
            return true;
        if (reftype == OriginRefType.OPERATION_PRE_MEASUREDBY)
            return true;
        if (reftype == OriginRefType.OPERATION_POST_WELLFORMED)
            return true;
        if (reftype == OriginRefType.OPERATION_ANONASSUMPTION)
            return true;


        return false;
    }

    public PosInSequent Pos() {
        return PosInSequent.createCfmaPos(PIO);
    }
}
