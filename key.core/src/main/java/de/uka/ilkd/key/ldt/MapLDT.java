/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.literal.EmptyMapLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;

import org.key_project.util.ExtList;

/**
 * LDT for maps.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public final class MapLDT extends LDT {

    public static final Name NAME = new Name("Map");

    public final Function mapEmpty;

    public MapLDT(TermServices services) {
        super(NAME, services);
        mapEmpty = addFunction(services, "mapEmpty");
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term[] subs,
            Services services, ExecutionContext ec) {
        return isResponsible(op, (Term) null, services, ec);
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right, Services services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, TermServices services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert lit instanceof EmptyMapLiteral;
        return services.getTermBuilder().func(mapEmpty);
    }

    @Override
    public Function getFunctionFor(Operator op, Services serv, ExecutionContext ec) {
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return f.equals(mapEmpty);
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        if (t.op().equals(mapEmpty)) {
            return EmptyMapLiteral.INSTANCE;
        }
        assert false;
        return null;
    }

    @Override
    public Type getType(Term t) {
        assert false;
        return null;
    }

    public Function getMapEmpty() {
        return mapEmpty;
    }

}
