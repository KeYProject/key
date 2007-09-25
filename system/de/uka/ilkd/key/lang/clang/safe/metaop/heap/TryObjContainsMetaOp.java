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
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Meta operation that tries to evaluate expression
 * <code>objContains(o1, o2)</code>, where <code>o1, o2</code> are of
 * object type. Evaluation is based on removing accessors at the top-level of
 * terms.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryObjContainsMetaOp extends SafeBaseMetaOp {

        public TryObjContainsMetaOp() {
                super(new Name("#ClangTryObjContains"), 1);
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

                if (!(term.sub(0).op() instanceof Function && term.sub(0).op()
                                .name().toString().equals("objContains")))
                        throw new IllegalArgumentException(
                                        "#TryObjContains first argument must be 'objContains' predicate");

                Term objContainsTerm = term.sub(0);
                Function objContainsFun = (Function) objContainsTerm.op();
                Term objTerm0 = objContainsTerm.sub(0);
                Term objTerm1 = objContainsTerm.sub(1);

                Term objEqTerm = TermFactory.DEFAULT
                                .createEqualityTerm(new Term[] { objTerm0,
                                                objTerm1 });

                if (objTerm1.op() instanceof RepositoryFunction)
                        return objEqTerm;

                if (objTerm1.op() instanceof ArrayRepositoryFunction)
                        return objEqTerm;
                
                if (objTerm1.op() == symbolEnv.getNullConstant())
                        return objEqTerm;                

                if (objTerm1.op() instanceof MemberFunction) {
                        Term structuredTerm = objTerm1.sub(0);
                        Term parentContainsTerm = TermFactory.DEFAULT
                                        .createFunctionTerm(
                                                        objContainsFun,
                                                        new Term[] { objTerm0,
                                                                        structuredTerm });

                        return TermFactory.DEFAULT.createJunctorTerm(
                                        Op.OR,
                                        new Term[] { objEqTerm,
                                                        parentContainsTerm });
                }

                if (objTerm1.op() instanceof ElemFunction) {
                        Term arrayTerm = objTerm1.sub(0);

                        Term parentContainsTerm = TermFactory.DEFAULT
                                        .createFunctionTerm(
                                                        objContainsFun,
                                                        new Term[] { objTerm0,
                                                                        arrayTerm });

                        return TermFactory.DEFAULT.createJunctorTerm(
                                        Op.OR,
                                        new Term[] { objEqTerm,
                                                        parentContainsTerm });
                }
                
                return objContainsTerm;
        }
}
