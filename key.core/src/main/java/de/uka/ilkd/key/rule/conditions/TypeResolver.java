/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;


/**
 * Several variable conditions deal with types. The type resolver provides a unique interface to
 * access types, e.g. the type of a schemavariable instantiation, the instantiated type of a generic
 * sort or the type an attribute is declared in.
 */
public abstract class TypeResolver {

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public static TypeResolver createContainerTypeResolver(SchemaVariable s) {
        return new ContainerTypeResolver(s);
    }

    public static TypeResolver createElementTypeResolver(SchemaVariable s) {
        return new ElementTypeResolverForSV(s);
    }

    public static TypeResolver createGenericSortResolver(GenericSort gs) {
        return new GenericSortResolver(gs);
    }

    public static TypeResolver createNonGenericSortResolver(Sort s) {
        return new NonGenericSortResolver(s);
    }


    public abstract boolean isComplete(SchemaVariable sv, SyntaxElement instCandidate,
            SVInstantiations instMap, TermServices services);

    public abstract Sort resolveSort(SchemaVariable sv, SyntaxElement instCandidate,
            SVInstantiations instMap, Services services);


    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    public static class GenericSortResolver extends TypeResolver {

        private final GenericSort gs;

        public GenericSortResolver(GenericSort gs) {
            this.gs = gs;
        }

        public GenericSort getGenericSort() {
            return gs;
        }

        @Override
        public boolean isComplete(SchemaVariable sv, SyntaxElement instCandidate,
                SVInstantiations instMap, TermServices services) {
            return instMap.getGenericSortInstantiations().getInstantiation(gs) != null;
        }

        @Override
        public Sort resolveSort(SchemaVariable sv, SyntaxElement instCandidate,
                SVInstantiations instMap, Services services) {
            return instMap.getGenericSortInstantiations().getInstantiation(gs);
        }

        @Override
        public String toString() {
            return gs.toString();
        }
    }

    public static class NonGenericSortResolver extends TypeResolver {

        private final Sort s;

        public NonGenericSortResolver(Sort s) {
            this.s = s;
        }

        @Override
        public boolean isComplete(SchemaVariable sv, SyntaxElement instCandidate,
                SVInstantiations instMap, TermServices services) {
            return true;
        }

        @Override
        public Sort resolveSort(SchemaVariable sv, SyntaxElement instCandidate,
                SVInstantiations instMap, Services services) {
            return s;
        }

        public Sort getSort() {
            return s;
        }

        @Override
        public String toString() {
            return s.toString();
        }
    }

    public static class ElementTypeResolverForSV extends TypeResolver {

        private final SchemaVariable resolveSV;

        public ElementTypeResolverForSV(SchemaVariable sv) {
            this.resolveSV = sv;
        }

        @Override
        public boolean isComplete(SchemaVariable sv, SyntaxElement instCandidate,
                SVInstantiations instMap, TermServices services) {
            return resolveSV == sv || instMap.getInstantiation(resolveSV) != null;
        }

        @Override
        public Sort resolveSort(SchemaVariable sv, SyntaxElement instCandidate,
                SVInstantiations instMap, Services services) {

            final Sort s;

            final SyntaxElement inst = (SyntaxElement) (resolveSV == sv ? instCandidate
                    : instMap.getInstantiation(resolveSV));

            if (inst instanceof ProgramVariable) {
                s = ((ProgramVariable) inst).sort();
            } else {
                JTerm gsTerm = null;
                if (inst instanceof JTerm) {
                    gsTerm = (JTerm) inst;
                } else if (inst instanceof ProgramElement) {
                    gsTerm = services.getTypeConverter().convertToLogicElement(
                        (ProgramElement) inst, instMap.getExecutionContext());
                } else {
                    Debug.fail("Unexpected substitution for sv " + resolveSV + ":" + inst);
                    return null;
                }
                s = gsTerm.sort();
            }
            return s;
        }

        @Override
        public String toString() {
            return "\\typeof(" + resolveSV + ")";
        }
    }


    public static class ContainerTypeResolver extends TypeResolver {

        private final SchemaVariable memberSV;

        public ContainerTypeResolver(SchemaVariable sv) {
            this.memberSV = sv;
        }

        @Override
        public boolean isComplete(SchemaVariable sv, SyntaxElement instCandidate,
                SVInstantiations instMap, TermServices services) {

            return sv == memberSV || instMap.getInstantiation(memberSV) != null;
        }

        @Override
        public Sort resolveSort(SchemaVariable sv, SyntaxElement instCandidate,
                SVInstantiations instMap, Services services) {
            final Sort result;

            final SyntaxElement inst = (SyntaxElement) (memberSV == sv ? instCandidate
                    : instMap.getInstantiation(memberSV));

            if (inst instanceof Operator) {
                result = getContainerSort((Operator) inst, services);
            } else {
                if (inst instanceof Expression) {
                    result = getContainerSort(services.getTypeConverter()
                            .convertToLogicElement((Expression) inst, instMap.getExecutionContext())
                            .op(),
                        services);
                } else if (inst instanceof JTerm) {
                    result = getContainerSort(((JTerm) inst).op(), services);
                } else {
                    Debug.fail("Unexpected instantiation for SV " + memberSV + ":" + inst);
                    result = null;
                }
            }
            return result;
        }

        private Sort getContainerSort(Operator op, TermServices services) {
            Sort result = null;
            if (op instanceof ProgramVariable) {
                result = ((ProgramVariable) op).getContainerType().getSort();
            } else if (op instanceof IObserverFunction) {
                result = ((IObserverFunction) op).getContainerType().getSort();
            } else if (op instanceof Function func && func.isUnique()
                    && op.name().toString().contains("::")) {
                // Heap
                String funcName = func.name().toString();
                String sortName = funcName.substring(0, funcName.indexOf("::"));
                return services.getNamespaces().sorts().lookup(new Name(sortName));
            } else {
                Debug.fail("Unknown member type", op);
            }
            return result;
        }

        @Override
        public String toString() {
            return "\\containerType(" + memberSV + ")";
        }
    }
}
