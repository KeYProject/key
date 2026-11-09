/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.literal.EmptyMapLiteral;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;

import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableList;

/**
 * LDT for maps.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public final class MapLDT extends ParametricLDT {

    public static final Name NAME = new Name("Map");

    public final ParametricFunctionDecl mapGet;
    public final ParametricFunctionDecl mapUndef;
    public final ParametricFunctionDecl mapForeach;
    public final ParametricFunctionDecl mapEmpty;
    public final ParametricFunctionDecl mapSingleton;
    public final ParametricFunctionDecl mapOverride;
    public final ParametricFunctionDecl pseq2map;
    public final ParametricFunctionDecl mapUpdate;
    public final ParametricFunctionDecl mapRemove;

    public MapLDT(TermServices services) {
        super(NAME, services);
        mapGet = addParametricFunction(services, "mapGet");
        mapUndef = addParametricFunction(services, "mapUndef");
        mapForeach = addParametricFunction(services, "mapForeach");
        mapEmpty = addParametricFunction(services, "mapEmpty");
        mapSingleton = addParametricFunction(services, "mapSingleton");
        mapOverride = addParametricFunction(services, "mapOverride");
        pseq2map = addParametricFunction(services, "pseq2map");
        mapUpdate = addParametricFunction(services, "mapUpdate");
        mapRemove = addParametricFunction(services, "mapRemove");
    }

    @Override
    public boolean isResponsible(Operator op, JTerm[] subs,
            Services services, ExecutionContext ec) {
        return isResponsible(op, (JTerm) null, services, ec);
    }

    @Override
    public boolean isResponsible(Operator op, JTerm left, JTerm right, Services services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm sub, TermServices services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public JTerm translateLiteral(Literal lit, Services services) {
        assert lit instanceof EmptyMapLiteral;
        return services.getTermBuilder().func(ParametricFunctionInstance.get(mapEmpty, ImmutableList.singleton(new GenericArgument(JavaDLTheory.ANY)), services));
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
    public Expression translateTerm(JTerm t, ExtList children, Services services) {
        if (t.op() instanceof ParametricFunctionInstance pfi && pfi.getBase().equals(mapEmpty)) {
            return EmptyMapLiteral.INSTANCE;
        }
        assert false;
        return null;
    }

    public ParametricFunctionDecl getMapGet() {
        return mapGet;
    }
    public ParametricFunctionDecl getMapUndef() {
        return mapUndef;
    }
    public ParametricFunctionDecl getMapEmpty() {
        return mapEmpty;
    }
    public ParametricFunctionDecl getMapForeach() {
        return mapForeach;
    }
    public ParametricFunctionDecl getMapSingleton() {
        return mapSingleton;
    }
    public ParametricFunctionDecl getMapOverride() {
        return mapOverride;
    }
    public ParametricFunctionDecl getMapRemove() {
        return mapRemove;
    }
    public ParametricFunctionDecl getMapUpdate() {
        return mapUpdate;
    }
    public ParametricFunctionDecl getPseq2map() {
        return pseq2map;
    }
}
