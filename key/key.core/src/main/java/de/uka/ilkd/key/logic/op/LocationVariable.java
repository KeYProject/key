package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class represents proper program variables, which are not program constants. See the
 * description of the superclass ProgramVariable for more information.
 */
public final class LocationVariable extends ProgramVariable implements UpdateableOperator {
    public LocationVariable(ProgramElementName name, KeYJavaType t, KeYJavaType containingType,
            boolean isStatic, boolean isModel, boolean isGhost, boolean isFinal) {
        super(name, t.getSort(), t, containingType, isStatic, isModel, isGhost, isFinal);
    }

    public LocationVariable(ProgramElementName name, KeYJavaType t, KeYJavaType containingType,
            boolean isStatic, boolean isModel) {
        super(name, t.getSort(), t, containingType, isStatic, isModel, false);
    }


    public LocationVariable(ProgramElementName name, KeYJavaType t) {
        super(name, t.getSort(), t, null, false, false, false);
    }


    public LocationVariable(ProgramElementName name, KeYJavaType t, boolean isFinal) {
        super(name, t.getSort(), t, null, false, false, false, isFinal);
    }

    public LocationVariable(ProgramElementName name, KeYJavaType t, boolean isGhost,
            boolean isFinal) {
        super(name, t.getSort(), t, null, false, false, isGhost, isFinal);
    }


    public LocationVariable(ProgramElementName name, Sort s) {
        super(name, s, null, null, false, false, false);
    }

    @Override
    public void visit(de.uka.ilkd.key.java.visitor.Visitor v) {
        v.performActionOnLocationVariable(this);
    }


    @Override
    public UpdateableOperator rename(Name name) {
        if (getKeYJavaType() != null) {
            return new LocationVariable(new ProgramElementName(name.toString()), getKeYJavaType(),
                getContainerType(), isStatic(), isModel());
        } else {
            return new LocationVariable(new ProgramElementName(name.toString()), sort());
        }
    }
}
