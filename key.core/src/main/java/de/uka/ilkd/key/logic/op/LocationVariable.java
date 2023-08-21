/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.Objects;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.EqualsModProofIrrelevancy;

/**
 * This class represents proper program variables, which are not program constants. See the
 * description of the superclass ProgramVariable for more information.
 */
public final class LocationVariable extends ProgramVariable implements UpdateableOperator,
        EqualsModProofIrrelevancy {
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

    @Override
    public boolean equalsModProofIrrelevancy(Object obj) {
        if (!(obj instanceof LocationVariable)) {
            return false;
        }
        LocationVariable that = (LocationVariable) obj;
        return Objects.equals(getKeYJavaType(), that.getKeYJavaType())
                && isStatic() == that.isStatic()
                && isModel() == that.isModel()
                && isGhost() == that.isGhost()
                && isFinal() == that.isFinal()
                && sort().equals(that.sort())
                && Objects.equals(argSorts(), that.argSorts())
                && name().toString().equals(that.name().toString())
                && arity() == that.arity()
                && Objects.equals(whereToBind(), that.whereToBind())
                && isRigid() == that.isRigid();
    }

    @Override
    public int hashCodeModProofIrrelevancy() {
        return Objects.hash(getKeYJavaType(), isStatic(), isModel(), isGhost(), isFinal(), sort(),
            argSorts(), name().toString(), arity(),
            whereToBind(), isRigid());
    }
}
