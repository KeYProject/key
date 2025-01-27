/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;

import java.util.*;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.ast.abstraction.*;
import org.key_project.rusty.ast.fn.Function;
import org.key_project.rusty.ast.ty.FnDefType;
import org.key_project.rusty.logic.op.ProgramFunction;

import org.jspecify.annotations.NonNull;

public final class RustInfo {
    private final Map<Type, KeYRustyType> type2KRTCache;
    private final Set<KeYRustyType> allTypes = new LinkedHashSet<>();
    private final Set<ProgramFunction> allFunctions = new HashSet<>();
    private final Map<Function, ProgramFunction> fnToProgFn;
    private final Services services;

    public RustInfo(Services services) {
        this.services = services;
        type2KRTCache = new HashMap<>();
        fnToProgFn = new HashMap<>();
    }

    public KeYRustyType getKeYRustyType(String name) {
        KeYRustyType result = getPrimitiveKeYRustyType(name);
        // TODO: ADTs etc.
        return result;
    }

    public KeYRustyType getKeYRustyType(Type type) {
        if (type2KRTCache.containsKey(type)) {
            return type2KRTCache.get(type);
        }
        if (type instanceof PrimitiveType pt) {
            return getPrimitiveKeYRustyType(pt);
        }
        if (type instanceof TupleType tt && tt == TupleType.UNIT) {
            var sort = services.getNamespaces().sorts().lookup("unit");
            var krt = new KeYRustyType(type, sort);
            type2KRTCache.put(type, krt);
            return krt;
        }
        if (type instanceof ReferenceType rt) {
            Sort sort = services.getMRefManager().getRefSort(rt.getSort(services), rt.isMut());
            var krt = new KeYRustyType(type, sort);
            type2KRTCache.put(type, krt);
            return krt;
        }
        if (type instanceof FnDefType ft) {
            var krt = new KeYRustyType(ft);
            type2KRTCache.put(type, krt);
            return krt;
        }
        if (type instanceof Never nt) {
            var krt = new KeYRustyType(nt);
            type2KRTCache.put(type, krt);
            return krt;
        }
        if (type instanceof Closure ct) {
            var krt = new KeYRustyType(ct);
            type2KRTCache.put(type, krt);
            return krt;
        }
        throw new IllegalArgumentException("Unsupported type: " + type);
    }

    private KeYRustyType getPrimitiveKeYRustyType(String name) {
        PrimitiveType type = PrimitiveType.get(name);
        if (type != null) {
            return getPrimitiveKeYRustyType(type);
        } else {
            return null;
        }
    }

    private KeYRustyType getPrimitiveKeYRustyType(PrimitiveType type) {
        if (type == null) {
            throw new IllegalArgumentException("Given type is null");
        }

        if (type2KRTCache != null && type2KRTCache.containsKey(type)) {
            return type2KRTCache.get(type);
        }
        Name ldtName = type.getCorrespondingLDTName();

        Namespace<@NonNull Sort> sorts = services.getNamespaces().sorts();
        Sort sort = sorts.lookup(ldtName);

        if (sort == null) {
            throw new IllegalStateException(
                "Could not find sort " + ldtName + " for type: " + type);
        }

        var result = new KeYRustyType(type, sort);
        if (type2KRTCache != null) {
            type2KRTCache.put(type, result);
        }

        return result;
    }

    public void registerType(Type type) {
        registerType(getKeYRustyType(type));
    }

    public void registerType(KeYRustyType type) {
        allTypes.add(type);
    }

    public void registerFunction(Function function) {
        if (!fnToProgFn.containsKey(function)) {
            var pf = fnToProgFn.computeIfAbsent(function,
                (fn) -> new ProgramFunction(fn, getKeYRustyType(fn.returnType().type())));
            allFunctions.add(pf);
        }
    }

    public ProgramFunction getFunction(Function function) {
        return fnToProgFn.get(function);
    }

    /**
     * returns all known KeYRustyTypes of the current program type model
     *
     * @return all known KeYRustyTypes of the current program type model
     */
    public Set<KeYRustyType> getAllKeYJavaTypes() {
        final Set<KeYRustyType> result = new LinkedHashSet<>();
        for (final var ty : allTypes) {
            var krt = getKeYRustyType(ty);
            if (krt != null) {
                result.add(krt);
            }
        }
        return result;
    }

    public Set<ProgramFunction> getAllFunctions() {
        return allFunctions;
    }
}
