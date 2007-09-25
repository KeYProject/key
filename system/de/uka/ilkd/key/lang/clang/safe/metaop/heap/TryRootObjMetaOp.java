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
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that tries to evaluate expression <code>rootObj(o)</code>,
 * where <code>o</code> is of object type. Evaluation is based on removing
 * accessors at the top-level of term <code>o</code>.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryRootObjMetaOp extends SafeBaseMetaOp {

        public TryRootObjMetaOp() {
                super(new Name("#ClangTryRootObj"), 1);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, 
                        IClangSafeEnvironment context) {
                ISymbolEnv symbolEnv = context.getSymbolEnv();

                if (!(term.sub(0).op() instanceof Function && term.sub(0).op()
                                .name().toString().equals("rootObj")))
                        throw new IllegalArgumentException(
                                        "#TryRootObj first argument must be 'rootObj' function");

                Term rootObjTerm = term.sub(0);
                Function rootObjFun = (Function) rootObjTerm.op();
                Term objTerm = rootObjTerm.sub(0);

                if (objTerm.op() instanceof RepositoryFunction)
                        return objTerm;

                if (objTerm.op() instanceof ArrayRepositoryFunction)
                        return objTerm;

                if (objTerm.op() instanceof MemberFunction) {
                        Term structuredTerm = objTerm.sub(0);
                        return TermFactory.DEFAULT.createFunctionTerm(
                                        rootObjFun, structuredTerm);
                }

                if (objTerm.op() instanceof ElemFunction) {
                        Term arrayTerm = objTerm.sub(0);
                        return TermFactory.DEFAULT.createFunctionTerm(
                                        rootObjFun, arrayTerm);
                }

                if (objTerm.op() == symbolEnv.getNullConstant())
                        return objTerm;

                return rootObjTerm;
        }
}
