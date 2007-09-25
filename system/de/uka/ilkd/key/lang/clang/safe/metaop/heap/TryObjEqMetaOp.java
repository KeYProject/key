package de.uka.ilkd.key.lang.clang.safe.metaop.heap;

import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.metaop.SafeBaseMetaOp;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ArrayRepositoryFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ElemFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.RepositoryFunction;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that tries to evaluate expression <code>e1 = e2</code>,
 * where <code>o1, o2</code> are of object type. Evaluation is based on
 * comparing accessors at the top-level of the terms.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryObjEqMetaOp extends SafeBaseMetaOp {

        public TryObjEqMetaOp() {
                super(new Name("#ClangTryObjEq"), 1);
        }

        /**
         * @inheritDocs
         */
        public Sort sort(Term[] term) {
                return Sort.FORMULA;
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, 
                        IClangSafeEnvironment context) {
                ISymbolEnv symbolEnv = context.getSymbolEnv();

                if (!(term.sub(0).op() instanceof Equality))
                        throw new IllegalArgumentException(
                                        "#TryObjEq should be applied to object equality formula");

                Term objEqTerm = term.sub(0);
                Term objTerm0 = objEqTerm.sub(0);
                Term objTerm1 = objEqTerm.sub(1);

                // If the sorts are incompatible
                if (!(objTerm0.sort().extendsTrans(objTerm1.sort()) || objTerm1
                                .sort().extendsTrans(objTerm0.sort()))) {
                        
                        if (objTerm0.sort().extendsTrans(context.getSafePlatform().getSafeArrayMarkerSort()) &&
                                        objTerm1.sort().extendsTrans(context.getSafePlatform().getSafeVoidSort()) &&
                                        !objTerm1.sort().extendsTrans(context.getSafePlatform().getSafeArrayMarkerSort()))
                                return TermFactory.DEFAULT                                        
                                        .createJunctorTerm(
                                                        Op.FALSE);
                        
                        if (objTerm1.sort().extendsTrans(context.getSafePlatform().getSafeArrayMarkerSort()) &&
                                        objTerm0.sort().extendsTrans(context.getSafePlatform().getSafeVoidSort()) &&
                                        !objTerm0.sort().extendsTrans(context.getSafePlatform().getSafeArrayMarkerSort()))
                                return TermFactory.DEFAULT                                        
                                        .createJunctorTerm(
                                                        Op.FALSE);
                        
                        if (objTerm0.sort().extendsTrans(context.getSafePlatform().getSafeVoidSort()) &&
                                        objTerm1.sort().extendsTrans(context.getSafePlatform().getSafeVoidSort()))
                        return TermFactory.DEFAULT
                                        .createJunctorTerm(
                                                        Op.AND,
                                                        TermFactory.DEFAULT
                                                                        .createEqualityTerm(
                                                                                        objTerm0,
                                                                                        TermFactory.DEFAULT
                                                                                                        .createFunctionTerm(symbolEnv
                                                                                                                        .getNullConstant())),
                                                        TermFactory.DEFAULT
                                                                        .createEqualityTerm(
                                                                                        objTerm1,
                                                                                        TermFactory.DEFAULT
                                                                                                        .createFunctionTerm(symbolEnv
                                                                                                                        .getNullConstant())));
                }
                if (!(objTerm0.op() instanceof RepositoryFunction
                                || objTerm0.op() instanceof ArrayRepositoryFunction
                                || objTerm0.op() instanceof MemberFunction
                                || objTerm0.op() instanceof ElemFunction || objTerm0
                                .op() == symbolEnv.getNullConstant())
                                || !(objTerm1.op() instanceof RepositoryFunction
                                                || objTerm1.op() instanceof ArrayRepositoryFunction
                                                || objTerm1.op() instanceof MemberFunction
                                                || objTerm1.op() instanceof ElemFunction || objTerm1
                                                .op() == symbolEnv
                                                .getNullConstant()))
                        return objEqTerm;

                if (objTerm0.op() != objTerm1.op())
                        return TermFactory.DEFAULT
                                        .createJunctorTerm(Op.FALSE);

                Term result = null;
                for (int i = 0; i < objTerm0.arity(); i++) {
                        Term eq = TermFactory.DEFAULT.createEqualityTerm(
                                        objTerm0.sub(i).sort()
                                                        .getEqualitySymbol(),
                                        new Term[] { objTerm0.sub(i),
                                                        objTerm1.sub(i) });

                        if (i == 0)
                                result = eq;
                        else
                                result = TermFactory.DEFAULT.createJunctorTerm(
                                                Op.AND,
                                                new Term[] { result, eq });
                }

                return result != null ? result : TermFactory.DEFAULT
                                .createJunctorTerm(Op.TRUE);
        }
}
